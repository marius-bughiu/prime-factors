# A product for which every negative target on the list fails

The search on ellipses tries to write multiples of a public number as $x^2+d y^2$ with $d>0$. Sometimes every choice from a large list is impossible, regardless of how far we search. For 2,336,879 this happens with every $d$ made by multiplying any number of primes up through 31, repetitions included. The signed search selects 2, 3 and 6. The very first target gives two useful solutions. [Lean proof and exact primes](../PrimeFactors/NegativeTargetObstruction.lean) · [Native benchmark](../benchmarks/signed-norm-arcs.json)

Here are the two solutions for $D=2$.

$$1679^2-2\cdot491^2=1721^2-2\cdot559^2=2{,}336{,}879.$$

The greatest common divisor of $1679\cdot559-1721\cdot491$ and the input is 1,871. Division gives 1,249. The worked input was selected to exercise the limitation of the earlier search. An independent eight-input comparison measures costs at two larger sizes. [Complete search measurements](scanning-signed-norm-arcs.md)

## Why changing the multiplier cannot rescue the negative targets

A point on $x^2+d y^2=mN$ whose denominator $y$ is invertible modulo $N$ would give a square root of $-d$ by division. But $N$ leaves remainder 3 modulo 4, so the Jacobi sign of $-1$ is negative. Every positive prime up through 31 has positive Jacobi sign at this $N$. Multiplying any selection of them preserves that positive sign, and multiplying by $-1$ makes it negative. Every modular square has nonnegative Jacobi sign. This rules out every such root, for every $m$. If a denominator already shares a proper divisor with $N$, the gcd itself yields a factor. Earlier implementations also check for such direct divisors. [General word exclusion](../PrimeFactors/NegativeTargetObstruction.lean) · [Earlier target selector](../experiments/norm_directions.py)

## The same obstruction with 1,024-bit primes

We also constructed a 2,048-bit product on which every prime up through 739 has positive public Jacobi sign, and −1 has negative sign. This rules out every negative target built by multiplying any of those 131 primes, however many times. It covers the entire collection of generators used in the earlier full-size ellipse benchmark. Positive target 2 does have a square root. A separate certificate checks that root, which we constructed from the known factors. The search using the product alone tried 64 blocks, found no point, and left the whole number unresolved. [Construction and checked results](../research/negative-menu-control.json) · [Reproducible Lean certificates](../experiments/negative_menu_control.py) · [Earlier full-size benchmark settings](../benchmarks/norm-directions.json)

Testing beyond the construction revealed its exact limit. Every negative target built from primes smaller than 773 still fails. Once 773 is allowed, −773 itself fails but $-7\cdot773$ has a square root. Lean also checked a root of −809. These roots were reconstructed using the known factors. [Exact boundary and witnesses](../research/negative-menu-control.json)

To construct the example, pick residues 7 and 1 modulo 8 for the two primes. For each odd prime $l\equiv1\pmod4$ up through 739, prescribe residue 1 for both. For each $l\equiv3\pmod4$, prescribe residue 1 on one side and a quadratic nonresidue on the other, alternating sides. Quadratic reciprocity then makes the two signs at $l$ agree when read at the hidden primes. The many prescribed residues equal to 1 also give enough known factors of each prime's predecessor to certify primality. This selection was designed specifically to make the earlier targets fail. [Generator and independent primality checks](../experiments/negative_menu_control.py)

On the fresh 2,048-bit comparison, the new rule guarantees at least one viable target, and the complete search visits more than $2^{685}$ blocks. We tested 64. No factor was found. The asymptotic bound of $O(N^{1/3})$ blocks improves on direct enumeration of these curves. Other deterministic integer factorization methods have published bounds with a smaller exponent. [Full-size budget and search results](../research/signed-norm-arcs.json) · [Harvey, exponent one-fifth algorithm](https://arxiv.org/abs/2010.05450)
