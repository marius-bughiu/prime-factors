# Checking neighboring remainders with one smaller lattice

Two factor remainders modulo $2^{614}$ fit in one remainder class modulo $2^{613}$. One rank-four lattice reduction now checks both children. The resulting trace has at most **six possible values**, each giving a quartic equation. Sometimes the trace has no possible value at all, and the entire parent can be discarded. In the fresh 2,048-bit comparison, two values remained and both quartics failed small-prime tests. That rejected the parent in 0.72 seconds. Testing the two children separately took 4.45 seconds. [Matched measurements](../research/projected-quartic-levels.json) · [Implementation](../experiments/projected_quartic_levels.py)

## Sieving whole blocks of levels for positive factors

For two positive factors of the same bit length, their sum occupies a narrower interval than the signed gap. Use the product to center $T=x+y-h$ and $Z=x-c$, then project the basis $1,T,Z,T^2-2s^2,ZT$ onto its last four coordinates. The positive window changes $W$ and the spread $S$. The projected index and the level equation $F(x)=jMx^2$ stay the same. [Centered intervals and coordinates](../experiments/centered_sum_quartic.py)

For any auxiliary prime $\ell$ coprime to $30RN$, a true factor is nonzero modulo $\ell$. Evaluate the small set
$$ A_\ell=\{F(z)/(M z^2)\bmod\ell : z=1,\ldots,\ell-1\} .$$
Every true level satisfies $j\bmod\ell\in A_\ell$. This follows by reducing the level equation at $z=x\bmod\ell$. The same condition applies to every level sharing that residue, so the solver evaluates the map once for each nonzero $z$. It stores the allowable levels as a repeated bit pattern of period $\ell$. Intersecting these patterns in blocks of 65,536 positions implements the simultaneous congruence test without building the full CRT modulus. If a whole block becomes zero, every level in it is ruled out. Primes that divide the input or the modulus are skipped. [Lean proof of the residue implication](../PrimeFactors/ProjectedQuarticLevels.lean) · [Sieve and reproducer](../experiments/projected_level_sieve.py)

We fixed remainder 1, a primary radix $2^{604}$ and a secondary radix $2^{600}$ in advance. Both controls used all 51 primes from 7 through 251 and 6,020 evaluations of the finite-field map per run. The cap was $2^{30}$ level positions. All four intervals were scanned completely. One lattice reduction was used per row. The table counts levels surviving the periodic masks before primitive quartic construction. Time includes the reduction, tables, scanning and root checks. Lean certificate verification was performed outside the search timing.

| Product | Radix | Fine positive groups covered | Level positions | Blocks rejected / scanned | Surviving levels | Search time |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Crossed | $2^{604}$ | 256 | 172,628 | 2 / 3 | 1 | 0.668 s |
| Fresh | $2^{604}$ | 128 | 25,487 | 1 / 1 | 0 | 0.736 s |
| Crossed | $2^{600}$ | 4,096 | 166,296,695 | 2,537 / 2,538 | 1 | 0.747 s |
| Fresh | $2^{600}$ | 2,048 | 23,967,979 | 366 / 366 | 0 | 0.761 s |

The earlier input-specific positive quartics used $2^{612}$ and $2^{611}$ on the crossed and fresh controls, respectively. Their two lifts exchanged by factor swapping cannot both belong to the chosen coarse class because $N\not\equiv1$ modulo either coarse radix on either product. This makes the fine-group counts in the table exact. Both crossed runs recovered the same Lean-certified primes. Both fresh runs rejected the entire selected positive group. At $2^{600}$ the fresh product, which is 7 modulo 8, has $2^{598}$ positive groups in total and $2^{598}-1$ remain unchecked. [Trace coefficients, surviving levels and remaining cofactor](../research/projected-level-sieve.json)

At $2^{600}$ on the fresh input the sieve performed 9,240 mask intersections spanning 605,115,912 logical bit positions in total, taking 0.022 seconds. The periodic tables occupied 3,351,845 bits of integer payload, about 409 KiB before Python object overhead. Bit-parallel rejection still visits the level interval block by block. At the narrower comparison radix $2^{606}$, three-run medians for periodic versus individual tests were 0.712 versus 3.116 seconds across 5,897 levels on the crossed control, and 0.769 versus 1.439 seconds across 979 levels on the fresh control. On the small 15- and 48-level comparisons, individual tests were faster because the setup cost exceeded the savings. All paired runs gave the same factor results. [Matched comparisons and work counters](../research/projected-level-sieve.json)

## Removing the constant coordinate

Take the signed Dickson traces $1,D,x,D^2-2s^2,xD$, where $D=x-y$, $s=\lfloor\sqrt{N/8}\rfloor$, $xy=N$ and the factors are within a factor of two. Guess $x\equiv u\pmod R$ with $R$ dyadic and $u$ odd. Assume $\gcd(N,30)=1$. The full trace lattice $L$ consists of coefficient vectors for which the quartic $F(X)=X^2T(X,N/X)$ is divisible by $M=360R^4$ everywhere on the lane with $\gcd(X,30)=1$. Its index is $I=M^5/(12960R^{10})$. [Coordinates and local congruences](unit-newton-lanes.md)

Ignore the constant coefficient in the lattice reduction. The kernel of this projection on $L$ is exactly $M\mathbb Z$ along the constant axis. Indeed a pure constant trace $a$ gives $F(X)=aX^2$ and there is an allowed $X$ coprime to $M$. Every projected vector has a lift to $L$, and all its lifts have the same constant coefficient modulo $M$. The projected lattice has index $I/M$ in $\mathbb Z^4$. This follows by counting the $M$ possible constant cosets above each quotient class of the projection. The integer implementation also checks that removing the constant row leaves exactly this determinant.

Let $W$ be the product of the four nonconstant column weights. Their scaled projected lattice has determinant $\Delta=WI/M$. For a nonzero vector let $Q$ be its nonconstant trace, and $S$ the sum of its weighted absolute coefficients, so $|Q(x,y)|\le S$ on the balanced signed region. Let $C$ be the reduced constant coefficient of a lift. Every true factor in the lane has $Q(x,y)+C=jM$ for an integer $j$, because $x$ is a unit modulo $M$. Only the multiples inside $[C-S,C+S]$ need testing.

Each admissible $j$ gives $F_j(X)=F(X)-jMX^2$. The change to Dickson coordinates is unimodular, so a nonzero projected vector has a nonzero nonconstant coefficient in the original factor coordinates. Thus **every $F_j$ is nonzero**, including at a matching level. Their product is a single exact polynomial covering the entire parent. If the interval is empty the product is 1. The implementation keeps the factors separate so it can reject a level whenever its primitive polynomial in $(X-u)/R$ has no root modulo one small prime. This check is valid for signed integer roots. [Level count, nonvanishing, degree, coverage and modular rejection in Lean](../PrimeFactors/ProjectedQuarticLevels.lean)

## Worst-case number of levels

In rank four, classical LLL with parameter $3/4$ gives a first vector of Euclidean length at most $2^{3/4}\Delta^{1/4}$. The weighted absolute sum is at most twice that length. Hence
$$(2S/M)^4\le 2^{11}\,W/(12960R^{10}).$$
For $N<2^{2048}$ the Dickson weight product is at most $2^{6142}$. At $R=2^{614}$ the right side is at most $2^{11}\cdot4/12960<1$, giving **at most one** level with a rank-four reduction. At $R=2^{613}$ replace 4 by 4096. The right side lies between $5^4$ and $6^4$, so the interval contains at most six multiples and the product has degree at most 24. These counts cover positive and negative factor representatives. [Weight bound](gap-polynomial-scale.md) · [LLL theorem](https://doi.org/10.1007/BF01457454)

If one instead obtains a shortest vector in the weighted absolute-sum norm, the four-dimensional ball has volume $2^4 S^4/4!$. Minkowski's convex body theorem gives $S^4\le4!\Delta$, allowing at most **four** levels and degree 16 at $R=2^{613}$. This is an existence bound for a different short-vector choice. The measured implementation used LLL. For each additional bit removed from the radix, the worst-case bound for $2S/M$ multiplies by $2^{5/2}$. Thus the saving in lattice reductions comes with more possible quartics, and it supplies no general shortcut for choosing the correct coarse remainder. [Minkowski theorem in Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Group/GeometryOfNumbers.html)

## Complete and capped comparisons

For $96{,}577$, the parent search visited all five signed, unordered classes at radix 32. Three had an empty level interval. The remaining two produced all three balanced pairs, $221\times437$, $247\times391$ and $299\times323$. The complete comparison used nine rank-five reductions at radix 64. The sums of per-group median times over three alternating runs were 1.09 ms for the parents and 3.59 ms for the children. Both searches were given the product alone. [Tests and direct enumeration](../tests/test_projected_quartic_levels.py)

For each 2,048-bit control we tested the frozen remainder 1, once per radix. At $2^{613}$ the crossed control took 0.70 seconds with the parent and 4.11 seconds for its two children combined. One of two levels survived the modular tests and yielded the known pair, which Lean certified. On the fresh control both levels failed, leaving the entire product unresolved. The parent uses a modular rejection step before root isolation. The measured child implementation uses direct integer-root isolation.

| Parent radix | Fine signed groups covered on each control | Crossed levels / sent to root isolation | Fresh levels / sent to root isolation |
| ---: | ---: | ---: | ---: |
| $2^{613}$ | 2 | 2 / 1 | 2 / 0 |
| $2^{612}$ | 4 | 8 / 1 | 8 / 0 |
| $2^{611}$ | 8 | 36 / 1 | 63 / 2 |
| $2^{610}$ | 16 | 146 / 3 | 304 / 1 |

The $2^{610}$ parent took 0.68 seconds on the crossed control and 0.79 seconds on the fresh control. The former returned the same checked factors. The latter left $2^{607}$ other signed groups unchecked. All large timings are single runs on one selected group per product. The data record the integer trace, its lifted constant, the weighted spread, the level interval and the work performed. [Exact receipts](../research/projected-quartic-levels.json)
