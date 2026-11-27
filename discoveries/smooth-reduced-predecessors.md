# Factoring when the reduced predecessors have small prime divisors

Three modular powers after setup find both 1,024-bit prime factors of one constructed 2,048-bit product. The same bounded method leaves two existing comparison products unresolved. It still proves something about each one, assuming it has two distinct 1,024-bit prime factors. Remove the greatest common divisor of the two primes’ predecessors. Each number left over has a prime divisor bigger than 13. The algorithm learns this from the public product alone. [Benchmark inputs and expected outcomes](../benchmarks/reduced-smooth-readout.json) · [Lean proof](../PrimeFactors/ReducedSmoothReadout.lean)

## What the product reveals

Write $N=pq$, $g=\gcd(p-1,q-1)$, $r=(p-1)/g$ and $s=(q-1)/g$. For a unit $a$ modulo $N$, set $v=a^{N-1}\bmod N$. The identity $N-1=q(p-1)+(q-1)$ gives $\gcd(p-1,N-1)=g$, and likewise at $q$. The multiplicative orders of $v$ modulo the two primes divide $r$ and $s$, respectively. Those two orders are coprime. All the computation uses ordinary residues modulo $N$. [Local order proofs](../PrimeFactors/ReducedSlopes.lean)

The search tries $a=2,3,\dots$ up to an explicit budget. A proper gcd of $a$ and $N$ finishes immediately. Otherwise it accepts the first $a$ with $v\ne1$. Set a smoothness bound $B$ and an upper bound $C$ on $p-1,q-1$. In the experiment $C=2^{1024}-1$. For every prime $\ell\le\min(B,C)$, in ascending order, take $e_\ell=\ell^{\lfloor\log_\ell C\rfloor}$. Starting at $v$, repeatedly raise the current residue to $e_\ell$ modulo $N$.

* If an update first gives 1, take the **preceding** residue $z$. Both preceding local orders divide $e_\ell$. They are coprime and at least one exceeds 1, so exactly one equals 1.
* If the updates finish without reaching 1, take the **final** residue $z$. A local order dividing the product $E=\prod e_\ell$ has reached 1 at that prime.
* Read out $d=\gcd(z-1,N)$ once. For an accepted base, this returns a proper factor exactly when at least one of the two initial local orders divides $E$. For the converse, a local coordinate that equals 1 at the readout has been killed by a prefix of $E$. [Split, converse and public gcd theorems](../PrimeFactors/ReducedSmoothReadout.lean)

In particular **every accepted base splits $N$ if either $r$ or $s$ is $B$-smooth**, meaning all its prime divisors are at most $B$. The search takes $N,B,C$ and its base budget. It needs no advance knowledge that this condition holds. If it completes the sweep and the readout gcd is 1, both $r$ and $s$ have prime divisors exceeding $B$. Their coprimality makes the two divisors distinct. Exhausting the base budget before finding an accepted base leaves this question open. [Formal smoothness coverage and exhaustion](../PrimeFactors/ReducedSmoothReadout.lean)

For example, $341=11\cdot31$ has $g=10$, $r=1$ and $s=3$. Base 2 gives $2^{340}\equiv1\pmod{341}$, so the search moves to 3. Its starting residue is 56. With $B=3,C=31$, raising 56 to 16 leaves 56, and raising it to 27 gives 1. Taking the gcd at the previous residue gives $\gcd(55,341)=11$. [Executable search](../experiments/reduced_smooth_readout.py)

## What comes from the Dirichlet GRH

The subgroup of units with $a^{N-1}=1$ has exactly $g^2$ members among $g^2rs$ units. It is proper since $p\ne q$. Lamzouri, Li and Soundararajan show, under Dirichlet GRH, that for $N\ge3000$ with no prime divisor below $(\log N)^2$, every proper subgroup omits a prime at most $(\log N)^2$. Two 1,024-bit primes meet these conditions. The bound on the first accepted base is below $(2048\log 2)^2<2{,}015{,}166$. The Lean theorem takes the paper’s finite subgroup conclusion as an explicit premise. The pinned RH repository’s Dirichlet zero-location statements motivated this use of the published inequality. The search checks acceptance directly, and each observed outcome is unconditional. [Lamzouri, Li and Soundararajan, Theorem 1.1(2)](https://arxiv.org/html/1309.3595v3#S1.SS1) · [Pinned Dirichlet statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean) · [Fermat-liar count](../PrimeFactors/ReducedSlopes.lean)

For independent uniform units the expected setup cost is already at most two trials, unconditionally. There is also an exact probability of splitting a *fixed* product with a uniform accepted unit. Set $u=\gcd(r,E)$ and $w=\gcd(s,E)$. Raising to $N-1$ maps the units uniformly onto a pair of cyclic groups of sizes $r,s$. The $E$-th power kills $u$ and $w$ members in those two groups. Inclusion–exclusion counts $us+wr-uw$ pairs killed in at least one coordinate. Removing the single global identity, which the setup rejects, gives

$$\Pr(\text{split}\mid\text{accepted})=\frac{us+wr-uw-1}{rs-1}.$$

This count is a paper consequence of the checked local-order criterion and elementary cyclic-group counting. Tests enumerate every unit for four small products. The formula contains the unknown $r,s$, so evaluating it for a population of independently selected 2,048-bit products requires additional information. [Arithmetic tests](../tests/test_reduced_smooth_readout.py)

## Work and full-size comparisons

For $D$ tested bases, setup costs at most $D$ gcds and $D$ modular powers with an exponent of at most $\lceil\log_2 N\rceil$ bits. The scan costs at most $\pi(B)$ modular powers with exponents of at most $b$ bits for $C=2^b-1$, one identity comparison per update, and a single additional gcd. Binary powering uses fewer than $2b$ modular multiplications per update. The implementation sieves primes with $O(B)$ storage, builds each prime power by repeated multiplication, and keeps a constant number of residues modulo $N$. The bound concerns search. Primality certificates and their replay take additional work. [Search implementation](../experiments/reduced_smooth_readout.py) · [Benchmark and proof generation](../scripts/reduced_smooth_benchmark.py)

The constructed product uses $g=2\cdot1{,}000{,}000{,}007$, $p=1+g\,2^{764}3^{143}5$ and $q=1+g\,7^{283}11^{52}13^5$. Both reduced predecessors are 993 bits. Each full predecessor contains the common prime $1{,}000{,}000{,}007$. An earlier search by order size has a sufficient table width greater than $2^{496}$ here. The present calculation uses the small prime divisors of the reduced orders. The earlier size bound says nothing about the first collision of this specific base. The construction selected the factors for this property. [Earlier order-size method](common-predecessors.md) · [Common-divisor factoring in Galbraith and McKee, §5](https://www.math.auckland.ac.nz/~sgal018/pair-mod-n.pdf)

| Product | $B$ | Updates | Exponent bits after setup | Reduced sweep | Ordinary sweep |
| --- | ---: | ---: | ---: | --- | --- |
| Constructed | 5 | 3 | 3,072 | Split at final residue, 0.043 s | No split, 0.027 s |
| Same constructed product | 13 | 6 | 6,140 | Split before identity, 0.072 s | No split, 0.056 s |
| Fresh comparison | 13 | 6 | 6,140 | Gcd 1, 0.069 s | No split, 0.054 s |
| Crossed comparison | 13 | 6 | 6,140 | Gcd 1, 0.069 s | No split, 0.054 s |

These illustrative timings measure search on a single machine. All four runs accepted base 2 on the first attempt. The ordinary $p-1$ comparison starts at the same base, uses the same prime-power blocks, takes a gcd at every block, and refines within a block if its gcd reaches $N$. The reduced sweep spends an additional initial power and base gcd. Both complete rows certify the same pair of primes. Every row also replays the accepted base, block list, modular powers and exact readout gcd in Lean. The ordinary control is a bounded implementation of the classical stage-one method. Other bases, stages and algorithms have separate cost models. [Pollard’s original method](https://doi.org/10.1017/S0305004100049252) · [Żrałek’s deterministic methods](https://arxiv.org/abs/0707.4102) · [Decimal fixtures](../benchmarks/reduced-smooth-readout.json)

Run the small example directly or regenerate the four rows as part of the normal benchmark.

```sh
python3 -m experiments.reduced_smooth_readout 341 --bound 3 --factor-bits 5 --base-limit 8
python3 scripts/benchmark.py
```
