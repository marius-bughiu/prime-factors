# How much does another prime-power digit remove?

Given the public product $N$, let $H_m(N)$ count the distinct residues $s$ for which $x+y=s$ and $xy=N$ are solvable modulo $m$. The true factor sum always survives. At an odd prime $p$ coprime to $N$, the surviving fraction at **every** power is at least $1/12$. This bound is sharp in the limit. We formalized the local count of Bower, Evans, Luo and Miller, including singular discriminants. Their paper uses the term *reduced coordinate sumset*. [Original paper, Theorems 3.3 and 3.6](https://arxiv.org/abs/1212.2930) · [Lean proofs](../PrimeFactors/PrimePowerCount.lean)

## Exact counts at odd primes

Write $e=k+1\ge1$. If $N$ is a quadratic nonresidue modulo $p$, there are $(p-1)/2$ admissible first digits and every one lifts in $p^k$ ways. The density stays $(p-1)/(2p)$ at every precision.

If $N$ is a nonzero square modulo $p$, there are $(p-3)/2$ regular admissible first digits and two colliding first digits. A collision means $x=y\bmod p$, or equivalently $s^2=4N\bmod p$. Define $c_k$ as the number of surviving lifts of **each** colliding digit. Then

$$
H_{p^{k+1}}(N)=\frac{p-3}{2}p^k+2c_k,\qquad
2(p+1)c_k=p^k+
\begin{cases}2p+1 & k\text{ even},\\ p+2 & k\text{ odd}.\end{cases}
$$

To see what the collision contributes, fix the first sum digit $r$. On that class $s\mapsto D=s^2-4N$ is injective. If two inputs $s,t$ have the same discriminant, $(s-t)(s+t)=0$ and $s+t\equiv2r\ne0\bmod p$ is a unit. The source and target first-digit classes each have $p^k$ elements, so the map reaches every discriminant in its target class. The admissible values there are exactly the squares. At precision $e\ge2$, every square reducing to zero is uniquely $p^2$ times a square residue modulo $p^{e-2}$, including zero itself. Thus a two-level recurrence counts singular lifts without ever enumerating factor pairs. The proofs use only $N\bmod p^e$. If the initial gcd yields a proper divisor, it already gives a split. [Fiber equivalence and exact cardinalities](../PrimeFactors/PrimePowerCount.lean) · [Earlier first-digit lifting](../PrimeFactors/PrimePower.lean)

For a square product the limiting density is $(p^2-2p-1)/(2p(p+1))$. At $p=3$ it equals $1/12$. The counts at $3,9,27,81,243,729$ are $2,2,4,8,22,62$. At $p\ge5$ the regular classes alone give density at least $1/5$. Lean checks the parity correction, the uniform $1/12$ inequality and this sequence. A single Legendre-symbol test, one exponentiation for $p^k$ and a fixed number of exact integer operations evaluate the closed form. After reducing $N$ modulo $p$, modular exponentiation for the character costs $O(\log p)$ modular multiplications and $p^k$ costs $O(\log(k+2))$ multiplications of integers of at most $O(e\log p)$ bits. [Closed-form and density theorems](../PrimeFactors/PrimePowerCount.lean)

## Including the prime two

For odd $N$, the published dyadic count at $e\ge5$ is $(2^{e-4}+(-1)^{e-1})/3+3$ if $N\equiv1\bmod8$, $2^{e-4}$ if $N\equiv5\bmod8$, and $2^{e-3}$ if $N\equiv3,7\bmod8$. At $e=1,2$ the count is one. At $e=3$ it is two if $N\equiv1\bmod4$ and one otherwise. At $e=4$ it is two. These results imply density at least $1/48$, so including higher powers of two improves on the density at two by at most a factor of 24. The dyadic formula here is taken from the published theorem. The new Lean count covers odd primes. [Bower et al., Theorem 3.3](https://web.williams.edu/Mathematics/sjmiller/public_html/math/papers/BowerEvansLuoMiller_ModHyper_70.pdf)

## Choosing levels under a modulus budget

Hittmeir previously used these counts to choose higher powers of small primes in a factorization sieve, including a worked example that compares upgrading 7 to 49 with introducing 11. The following optimization fixes the resource as the binary width of the complete modulus. [Hittmeir, Theorem 3.5 and Example 4.7](https://arxiv.org/pdf/2205.10074#page=10)

For $M=\prod p^{e_p}$ coprime to $N$, CRT gives $H_M/M=\prod H_{p^{e_p}}/p^{e_p}$. To optimize this density under $M<2^B$, take each allowed prime once and consider all its exponent choices, including zero. Maintain pairs consisting of the modulus and its density. Discard a pair when another partial choice has both a smaller or equal modulus and a smaller or equal density. Every later prime multiplies both pairs by the same two positive quantities, which proves this pruning preserves an optimum. Exact fractions and the integer modulus cap avoid rounding errors. The Pareto frontier can have many states, and listing every prime below $2^B$ can cost exponential time in $B$. The procedure is appropriate for a bounded menu. [CRT for modular hyperbolas, Proposition 2.1](https://arxiv.org/abs/1212.2930)

For $N=1{,}000{,}036{,}000{,}099$, exhaustive enumeration gives the following minima. Each entry is the unreduced survivor count divided by the chosen modulus. The two odd-only columns show the gain from collisions without a dyadic filter.

| Maximum modulus width | Odd squarefree | All odd | Squarefree including 2 | All moduli |
|---:|---:|---:|---:|---:|
| 6 bits | 9/35 | 6/63 | 6/42 | 3/56 |
| 8 bits | 36/231 | 14/225 | 18/210 | 4/216 |
| 10 bits | 108/1001 | 36/945 | 54/910 | 6/504 |

This independent replay enumerates the modular pairs directly. It uses only the public product.

```python
from fractions import Fraction
from math import gcd, isqrt

N = 1_000_036_000_099
rows = []
for m in range(1, 1024):
    if gcd(m, N) != 1:
        continue
    residues = {(x + N * pow(x, -1, m)) % m for x in range(m) if gcd(x, m) == 1}
    squarefree = all(m % (d*d) for d in range(2, isqrt(m) + 1))
    rows.append((Fraction(len(residues), m), m, len(residues), squarefree))
for bits in (6, 8, 10):
    for odd, sf in ((True, True), (True, False), (False, True), (False, False)):
        _, m, h, _ = min(row for row in rows if row[1] < 2**bits
                         and (not odd or row[1] % 2) and (not sf or row[3]))
        print(bits, m, h)
```

**A bound on the improvement at equal budgets.** Write $\rho_m=H_m/m$. The ratio $\rho_p/\rho_{p^e}$ is one in the nonresidue case. For a square product at an odd prime the limiting density gives the upper bound $(p+1)^2/(p^2-2p-1)=1+4/p+O(p^{-2})$. Consequently, for every $M<2^B$ the ratio $\rho_{\operatorname{rad}(M)}/\rho_M$ is $O((\log(B+2))^4)$, uniformly in $N$. Indeed, sum the logarithms of the local ratios. For primes up to $B$, Mertens' theorem gives $\sum 1/p\le\log\log B+O(1)$. There are at most $B\log 2/\log B$ prime divisors above $B$, so those reciprocals contribute $O(1)$ altogether. The dyadic contribution is bounded by 24. The radical meets the same cap, so the optimal squarefree density divided by the optimal unrestricted density obeys the same bound. This comparison is a paper deduction from the local formulas and Mertens' theorem. [Verified Mertens theorem](https://isa-afp.org/browser_info/current/AFP/Prime_Distribution_Elementary/PNT_Consequences.html) · [Local count](../PrimeFactors/PrimePowerCount.lean)

The optimizing objective is the survivor fraction over a whole period. An interval of $W$ consecutive sums contains between $\lfloor W/M\rfloor H_M$ and $\lceil W/M\rceil H_M$ survivors. Actual counts can therefore differ when the period exceeds a short search interval. Constructing or searching a wheel of $H_M$ residues incurs additional work. Recovering a balanced 2048-bit factor sum efficiently from its local constraints remains open. [Existing interval and table bounds](searching-the-balanced-interval.md)
