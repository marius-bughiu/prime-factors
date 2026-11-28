# How often the public square grid finds a factor

Fix one product of two distinct 1,024-bit primes. Pick an eligible target uniformly at random. Lean proves that more than 90% of those targets reveal a factor somewhere in the square grid chosen from the product. The same grid has at least $2^{511}$ entries along each edge. Even if we could pick a different rectangular shape for every target for free, shrinking the two lists to $2^{256}$ entries in total drops coverage below one in $2^{511}$. [Full-grid theorem](../PrimeFactors/CircleMarkPublicDiskRate.lean) · [List-budget theorem](../PrimeFactors/CircleMarkGridWorkBudget.lean)

## What counts as a hit?

Given the product $N$, take $h=\lfloor\sqrt[4]{N}\rfloor$. An eligible target is a residue $a$ with Jacobi symbol $(a/N)=-1$, a condition we can check using $N$ alone. For each pair of integers $1\le i,j\le h$ the scalar test computes $\gcd(N,|i^2-aj^2|)$. The target is a square modulo exactly one of the primes. Consequently a successful gcd returns that prime. Several cells can give the same answer.

For example, $2{,}183=37\times59$ gives $h=6$ and 1,044 eligible targets. Exactly 522 targets produce 37, 414 produce 59, and 108 miss. Trying the first eligible positive integer picks 5. All 36 cells miss for that target, even though the chance of success with a uniform target is $26/29$. [Exhaustive counts](../benchmarks/public-grid-targets.json) · [Gcd interpretation](../PrimeFactors/CircleMarkRationalProduct.lean)

## Why the large square covers more than nine in ten targets

Write $p<q$ for the hidden primes. Exactly half the eligible targets are squares modulo $p$. The choice of side length ensures that the grid reaches every one of those targets. For the other half we need to count distinct nonzero values of $(i/j)^2$ modulo $q$. Each such value adds $1/(q-1)$ to the overall hit rate. [Exact contribution from each prime](../PrimeFactors/CircleMarkPublicGridRate.lean)

Inside the disk $i^2+j^2<q$, each positive pair with coprime coordinates gives a different square. To see why, suppose two reduced fractions $i/j$ and $k/l$ have equal squares modulo $q$. Then $il$ agrees with either $kj$ or $-kj$ modulo $q$. Cauchy–Schwarz gives $il+kj<q$ in this disk. The negative sign is impossible and the positive sign forces $il=kj$, so the two reduced fractions coincide. This adapts the short-vector argument of Böhm, Decker, Fieker and Pfister to squared fractions. [Lean proof](../PrimeFactors/CircleMarkRationalDisk.lean) · [Rational reconstruction, Lemma 4.2](https://arxiv.org/pdf/1207.1651#page=6)

The disk extends past two edges of the public square. To count points inside both shapes, the proof uses 105 disjoint strips of integer width $m=\lfloor\sqrt{q-1}/125\rfloor$. Their exact point count is $10{,}394m^2$. Finite inclusion–exclusion through divisor 160, with an explicit bound for the tail and for rounding in the strips, leaves more than $2(q-1)/5$ coprime pairs. Adding the smaller prime’s half gives the claimed 90%. The hidden prime sets the scale only in the proof of coverage. The public grid uses $N$ alone. The argument is unconditional. The earlier analytic bound on locating a negative-Jacobi prime concerns target selection, and gives no uniformity guarantee for the first target. [Staircase geometry](../PrimeFactors/CircleMarkDiskStaircase.lean) · [Finite coprime counts](../PrimeFactors/CircleMarkPrimitiveDensity.lean) · [Analytic assumptions](../docs/research.md)

Outside the disk, the larger prime still satisfies $h^2<q$. Two *distinct* reduced cells then yield the same square exactly when $il+kj=q$. Each cell can have at most one opposite partner. At $2{,}257=37\times61$, the $6$-by-$6$ grid has 23 reduced fractions. Since $5^2+6^2=61$, the cells $(5,6)$ and $(6,5)$ form an opposite pair. It is the only pair, leaving 22 squares modulo 61. Detecting such pairs with the hidden prime explains the count after factorization. [Exact collision criterion and count](../PrimeFactors/CircleMarkGridCollisions.lean)

## How much work is hidden by the hit rate?

Fix any ordering of the cells using only the product. Even after the first $2^{1020}$ individual tests, fewer than a quarter of eligible targets have hit. More than 65% of *all* eligible targets miss these tests and succeed later in the full square. Among targets that succeed somewhere, more than $13/18$ succeed only later. The bound follows because each cell can cover at most one square at each prime. It concerns fixed scalar scans. Choosing cells after seeing the target or batching many cells in one calculation changes the cost model. [Scalar cost theorem](../PrimeFactors/CircleMarkGridScalarCost.lean)

A direct scan can visit $h^2$ cells. Give a planner two positive integer lists starting at 1 and allow their lengths $H,D$ to vary with the target, subject to $H+D\le L$. Every cell the planner could possibly reach lies in the triangle $i+j\le L$. There are exactly $L(L-1)/2$ positive cells. After removing proportional copies, the number of distinct fractions is $T=\sum_{k=2}^{L}\varphi(k)$, since fixing $i+j=k$ leaves precisely the numerators coprime to $k$.

If $2L^2<\min(p,q)$, Lean proves that the fraction of targets reachable by **any** permitted shape is exactly $T(1/(p-1)+1/(q-1))$. For $L\le2^{256}$ and the stated prime widths it is below $2^{-511}$. This grants the planner its best shape, even with knowledge of the answer. The budget measures the lengths of these two consecutive lists. Batched evaluation and other factoring methods have different costs. [Exact formula, shape selection and size bound](../PrimeFactors/CircleMarkGridWorkBudget.lean)

## What happened on small products?

We included every pair of distinct $w$-bit primes whose product has $2w$ bits for $w=6,\ldots,11$. This gives 7,995 products. For each, the two prime labels independently determine the exact uniform-target success rate by the Chinese remainder theorem. The searches themselves receive only the product. For three worked examples we also checked every eligible target by direct gcds. [Reproducible census](../experiments/public_grid_targets.py) · [Counts by width and region](../benchmarks/public-grid-targets.json)

| Choice or comparison | Observed result |
| --- | ---: |
| Uniform eligible target, giving every product equal weight | 98.36% mean hit rate |
| First eligible positive target | 7,676 hits and 319 misses |
| First target when $q>(h+1)^2+h$ | 5,043 hits in 5,362 products |
| Grid succeeded and the first five Fermat midpoint tests missed | 3,806 products |
| Five Fermat midpoint tests succeeded and the first-target grid missed | 44 products |
| Scalar work for first-target grids through a hit or exhaustion | 20,620 Jacobi tests and 6,678,239 gcds |
| Fermat midpoint tests through recovery of every pair | 98,963 tests |

At $32{,}881=131\times251$, the first eligible target is 11. Cell $(12,5)$ gives $|12^2-11\cdot5^2|=131$ on the 64th gcd. Fermat’s first square occurs on its tenth midpoint test. At $134{,}773=307\times439$, all 361 gcds at the first target, 2, miss, while Fermat recovers both primes on its sixth midpoint. These are counts of different operations. The census does not measure wall-clock speed or predict a runtime for 2,048-bit inputs. [Direct comparison data](../benchmarks/public-grid-targets.json) · [Factor certificate fixture](../benchmarks/cases.json)
