# Testing the same remainder on a fresh 2,048-bit product

The guess that found the factors in the crossed example missed both primes on a fresh product. We fixed the guess $x\equiv1\pmod{2^{616}}$, the generation rule, the two hash streams and the sample size of one before drawing the new primes. The first product was kept. The search received the product alone. It checked one group in 2.28 seconds, returned no pair and left the whole product unresolved. Lean independently checked the two construction primes and their product. [Earlier result](testing-one-factor-remainder.md) · [Construction record](../research/certified-control.json) · [Lean certificate](../benchmarks/controls/PocklingtonControl.lean)

## How the product was chosen

Each prime has 1,024 bits and lies between $3\cdot2^{1022}$ and $2^{1024}-1$. This fixes the leading two bits of each prime, makes the product exactly 2,048 bits and bounds their ratio by $4/3$. To generate a $b$-bit prime $P$, recursively generate a prime $r$ of $\lceil b/2\rceil+1$ bits. Draw $K$ from the entire integer interval for which $P=1+2Kr$ has the required size. A 10-bit leaf is certified by trial division. At the top, $r$ has 513 bits and $K$ has 510 or 511 bits. Oddness is required and there is no test that either prime has a particular low-bit pattern.

Candidates come from SHAKE256 applied to the ASCII string `prime-factors/certified-control/v1/{side}/{bits}/{counter}`. Each side and size starts its own counter at zero. The generator takes the needed low bits of the big-endian digest and discards offsets outside the interval. It rejects small-prime divisors, then accepts the first candidate whose base-two witness passes the order test below. The sampler is nonuniform over 1,024-bit primes. In particular, the size of a prime divisor of each predecessor is specified in advance. Recursive generation from a certified predecessor is classical. The fixed interval and multiplier sampling rule are recorded here to make this comparison reproducible. [Generator](../experiments/certified_control.py) · [Maurer, *Fast Generation of Prime Numbers*](https://crypto.ethz.ch/pubs/Maurer95a)

## What Lean checked

For each parent the certificate gives $z=2^{2K}\bmod P$. Lean checks $z^r=1\bmod P$, $\gcd(z-1,P)=1$, $P\le r^2$ and a certificate for the prime $r$. Every prime divisor of $P$ must then be $1\bmod r$ because the reduced $z$ has order $r$. A composite $P$ would have a prime divisor at most $\sqrt P\le r$, a contradiction. Each of the two chains uses seven such steps. The final theorem checks the product against the two prime labels. The separate size theorem checks both 2,048-bit bounds. The 7,753-byte Lean file is generated from the construction data and needs no factoring search to verify it. [Partial-order theorem](../PrimeFactors/PartialOrder.lean) · [Standalone certificate](../benchmarks/controls/PocklingtonControl.lean)

## What the search saw

Both top-level multipliers had 511 bits. Direct inspection of the construction labels after generation gives $v_2(p-1)=1$ and $v_2(q-1)=4$. The earlier crossed example had a prime with 984 such bits. For the new product, the degree-four calculation used one lattice reduction, 1,917 basis swaps, 3,055 size reductions and one root-search node. It found no integer root in the factor window. Since $N\equiv7\pmod8$, the factor-swap operation has no fixed odd residue modulo $2^{616}$, giving exactly $2^{614}$ unordered groups. The search left $2^{614}-1$ groups untested. One fresh input establishes the outcome of this guess on that product. [Product-only search](../experiments/unit_factor_lane.py)

On a sequential arm64 Mac replay with the Lean dependencies already built, generating both chains took 0.295 seconds, checking the certificate took 1.601 seconds and checking the one factor remainder took 2.280 seconds. The first separate kernel run took 8.203 seconds while other work was running. The factorization theorem's axiom report lists exactly `propext`, `Classical.choice` and `Quot.sound`.

From the repository root, these commands replay discovery with just the published input, regenerate the construction in memory, check it against the stored files and fixture, then run the Lean checker. The generator and certificate contain the factor labels.

```sh
python3 -c 'import json; from experiments.unit_factor_lane import search; cases=json.load(open("benchmarks/quartic-factor-lanes.json")); n=next(c["n"] for c in cases if c["id"]=="unit-lane-fresh-2048"); print(search(int(n)))'
python3 -m experiments.certified_control --verify
lake env lean -DwarningAsError=true benchmarks/controls/PocklingtonControl.lean
```
