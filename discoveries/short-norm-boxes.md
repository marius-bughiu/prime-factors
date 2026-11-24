# Which coordinates can a short norm search skip?

Every product of two distinct odd primes has a factor that appears in one of three short expressions. We can remove **all even first coordinates** and at least half the total polynomial degree plus evaluation count of the earlier full-size balanced search, up to endpoint rounding. On 1,900,014,700,027, the new search used 698 first coordinates and 697 evaluations to find the prime 1,900,009. On the 2,048-bit control the smaller table still needs roughly $5.81\times10^{153}$ first coordinates. [Earlier three-form construction](norm-orbits.md) · [Compressed search](../experiments/short_norm_boxes.py) · [Fixtures](../benchmarks/short-norm-boxes.json)

## How parity halves the polynomial degree

Let $p$ be the smaller prime, $U=\lfloor\sqrt N\rfloor$ and $L=\lfloor\sqrt U\rfloor$. For each square discriminant $b$ modulo $p$, the earlier bounded-slope argument gives positive $u,v\le\lfloor\sqrt p\rfloor$ satisfying $u^2\equiv bv^2\pmod p$. Using $b=-1,-2,2$ according to $p\bmod8$ yields *exact* prime representations in a smaller box.

| Residue of $p$ modulo 8 | Exact equality | First coordinate | Second coordinate |
|---|---|---|---|
| 1 or 5 | $p=t^2+a^2$ | odd | even |
| 3 | $p=t^2+2a^2$ | odd | odd, $a^2\le(U-1)/2$ |
| 7 | $p=2a^2-t^2$ | odd | even, $2a^2\ge p+1$ |

For the first row, the positive multiple $u^2+v^2$ is strictly below $2p$ since $p$ is prime and both squares are strictly below $p$. The sum is $p$. Put its odd coordinate first. For the second row the multiple $u^2+2v^2$ lies between zero and $3p$. If it equals $2p$, then $u$ is even and $p=v^2+2(u/2)^2$. An odd first coordinate has square 1 modulo 8, so $p\equiv3\pmod8$ forces the second one to be odd. For the third row, $-2p<u^2-2v^2<p$ and equality to zero is impossible since $\sqrt2$ is irrational. The multiple is $-p$. Reducing modulo 8 forces the stated parities. All the coordinate changes stay inside the original box. The square classes used here follow from the supplementary laws of quadratic reciprocity. [Local box and nonzero indefinite form](../PrimeFactors/NormOrbit.lean) · [Lean proof of normalization and parity](../PrimeFactors/ShortNormBox.lean)

Build one polynomial with roots $t^2$ at the odd first coordinates $1\le t\le L$. For each allowed $a$, evaluate that polynomial at $ba^2\bmod N$. A gcd of the product of its evaluations with $N$ detects a hit. When the gcd equals $N$, individual rows and leaves can still identify a proper factor. A complete scan must contain a leaf equal to $p$ or $-p$. Other leaves may reveal a factor earlier.

The program may also use the input promise $p<q\le2p$. This gives $P_0=\lceil\sqrt{N/2}\rceil\le p$. In the third row $a>L2^{-3/4}$ because $2a^2\ge P_0+1$ and $P_0\ge L^2/\sqrt2$. The three forms together therefore need degree $L/2+O(1)$ and at most
$$
\left(\tfrac12+\tfrac{1}{2\sqrt2}+\tfrac{1-2^{-3/4}}2\right)L+O(1)
$$
evaluation points, about $1.0563L$. The earlier full grid had degree $L$ and $3L$ evaluations. When a user caps both coordinates at $H<L$, the same exact equalities can exclude additional columns. For example, the positive form $t^2+2a^2$ must reach $P_0$ even when $t$ is the largest allowed odd coordinate.

## Choosing one of the three expressions after seeing the product

If a discriminant has Jacobi symbol $-1$ modulo $N$, exactly one of the two hidden primes admits its square root. This prime can be the larger one. The balance promise bounds it by $\sqrt{2N}$, so use side $S=\lfloor(2N)^{1/4}\rfloor$. With $N\equiv3,7\pmod8$, the Gaussian choice $b=-1$ separates the primes. It takes at most $\lceil S/2\rceil$ odd first and $\lfloor S/2\rfloor$ even second coordinates. With $N\equiv5\pmod8$, $b=2$ separates the primes and its exact identity gives $2a^2=t^2+s$ for the split prime $s$. The first coordinate is odd and $a>S/2$ because $s\ge P_0\ge S^2/2$. Thus both counts are at most $\lceil S/2\rceil$ in this case too. With $N\equiv1\pmod8$ the three-form count above applies. The implementation prices the applicable complete plans and chooses the least degree plus number of evaluation points, with precedence for plans fully covered by the cap. A budget can expire with either plan. [Exact planner and modular polynomial evaluations](../experiments/short_norm_boxes.py)

## Measured comparison

Both methods receive the same product and coordinate cap of 2,000. The balanced runs additionally receive the same promise $q\le2p$. Counts stop after finding the factor. Timings are medians of seven local runs of the search alone.

| Search on the 41-bit product | Polynomial degree | Evaluations | Coordinate pairs covered | Search time |
|---|---:|---:|---:|---:|
| Three ordinary forms | 1,174 | 2,348 | 2,756,552 | 124 ms |
| Three parity-restricted forms | 587 | 1,002 | 588,174 | 45 ms |
| Ordinary form chosen with balance | 1,396 | 1,396 | 1,948,816 | 78 ms |
| Parity-restricted form chosen with balance | 698 | 697 | 486,506 | 33 ms |

The two three-form searches found $151^2+2\cdot699^2=1{,}000{,}003$. Using the promise, the ordinary search found $1320^2+397^2=1{,}900{,}009$, and the compressed one found $2\cdot1055^2-571^2=1{,}900{,}009$. On the established 2,048-bit control, the complete three-form plan would reduce the degree from $1.1621\times10^{154}$ to $5.8103\times10^{153}$ and the evaluations from $3.4862\times10^{154}$ to $1.2274\times10^{154}$. These are computed table dimensions. The actual control run stopped at side 128. The public lower bound on the prime excludes every exact form there, so it built no polynomial and returned the original cofactor. [Inputs and decimal factor expectations](../benchmarks/short-norm-boxes.json) · [Exhaustive checks for small primes](../tests/test_short_norm_boxes.py)

On a separately sampled 63-bit semiprime, the parity-restricted search found a factor in 5.32 seconds. The ordinary balanced search over odd candidate divisors found the same factor in 3.66 seconds. The 41-bit timing measures savings over the older quadratic-form grid. The 63-bit comparison keeps the stronger direct-search baseline visible. [Paired work counts, timings and input](../research/norms-ordinary-63.json)

## One arbitrary separating coefficient and the probability of an early hit

A single separating coefficient also works for $N\equiv1\pmod8$. Sample $b$ uniformly from $1,\ldots,N-1$. A nonunit gives a proper divisor immediately. Otherwise retain $b$ when its Jacobi symbol is $-1$. Exactly half of the units qualify, by CRT, so the expected number of trials until either outcome is at most two for **every** pair of distinct odd primes. Coprime coefficients returned by this procedure are uniform on the separating set. Even a coefficient as large as $N-1$ works. For each positive $v$ smaller than both primes, $u^2-bv^2$ never vanishes modulo the prime at which $b$ is a nonsquare. Consequently no batch assembled from such leaves can have gcd $N$. Side $S$ above covers whichever prime splits. The sampled-coefficient argument uses all positive coordinates. The parity savings above exploit exact prime identities for three specific coefficients. [Lean inert-prime lemma](../PrimeFactors/NormOrbit.lean)

A deterministic selector can scan the integers, checking Jacobi symbols and gcds. Pollack proves unconditionally that for any $\epsilon>0$ and all sufficiently large moduli $m$, every nonprincipal Dirichlet character has a prime nonresidue below $m^{1/(4\sqrt e)+\epsilon}$. The Jacobi character modulo the distinct-prime product $N$ is nonprincipal by CRT. The asymptotic setup cost is therefore lower-order than an $N^{1/4}$ table for sufficiently small fixed $\epsilon$. This result supplies no explicit 2,048-bit cutoff here. Under Dirichlet GRH, the subgroup-escape bound instead gives a prime at most $\lceil(2048\log 2)^2\rceil=2{,}015{,}166$ for the stated prime sizes. The bounded deterministic selector reports how many candidates it checked. [Pollack, Theorem 1.1](https://arxiv.org/abs/1508.05035) · [Lamzouri, Li and Soundararajan, Theorem 1.1](https://arxiv.org/abs/1309.3595) · [Bounded selector](../experiments/universal_norm_batch.py)

For a uniform separating coefficient and $2H^2<\min(p,q)$ there is an exact success probability below the full table width. Let $C_H$ count ordered coprime pairs in $[1,H]^2$. Conditional on $p$ being the split prime, $b\bmod p$ is uniform among the $(p-1)/2$ nonzero squares. The residues $(u/v)^2$ generated by the box take exactly $C_H$ distinct values. Reduce each fraction first. Two reduced positive fractions with the same squared residue would have a cross-product difference or sum divisible by $p$. The sum is strictly between zero and $p$ and the absolute difference is below $p$. Thus the difference must vanish, and the fractions coincide. Each orientation of the split prime has probability $1/2$. The chance of a factor is exactly
$$
P_H=C_H\left(\frac1{p-1}+\frac1{q-1}\right).
$$
For $r$ independent uniform separating coefficients the success probability is $1-(1-P_H)^r$. For $H=2^{450}$ on the target prime sizes, $C_H\le H^2$ gives $P_H\le2^{-122}$. This calculation explains the cost of shrinking that random-coefficient box. It uses no independence assumption between different leaves of a single table. [Lean cross-product separation](../PrimeFactors/NormOrbit.lean) · [Direct enumeration of the finite probability](../tests/test_short_norm_boxes.py)
