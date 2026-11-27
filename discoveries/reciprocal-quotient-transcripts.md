# What do the early quotients of both factors reveal?

Suppose only the product $N=pq$ is given, with $p\le q$. Choose a public scale $M$ and try to locate the two reciprocals $M/p$ and $M/q$ in continued-fraction intervals. If there are $k$ intervals for the first reciprocal and $l$ for the second, a single ordered sweep needs at most **$k+l-1$ comparisons**. On the fresh 2,048-bit example, 256 intervals per reciprocal required only 49 comparisons. All of its more than $2^{1019}$ admissible smaller-factor locations survived the subsequent modulus-24 test. [Lean proof](../PrimeFactors/ReciprocalPrefixPairs.lean) · [Reproducible sweep](../experiments/reciprocal_prefix_pairs.py)

## Projecting both intervals onto one coordinate

For a possible smaller factor $x$, the product forces the larger *real* coordinate to equal $N/x$. Thus the two reciprocal values are $M/x$ and $Mx/N$. The first decreases and the second increases as $x$ grows. Trying a pair of intervals amounts to guessing a prefix for each reciprocal, with its rational endpoints known. Given brackets $[a/b,c/d)$ and $[e/f,g/h)$ with positive endpoints, all possible integer values of $x$ form one consecutive interval. Its endpoints are
$$
L=\max\!\left(\left\lfloor\frac{Md}{c}\right\rfloor+1,\;\left\lfloor\frac{eN-1}{Mf}\right\rfloor+1\right),\qquad
R=\min\!\left(\left\lfloor\frac{Mb}{a}\right\rfloor,\;\left\lfloor\frac{gN-1}{Mh}\right\rfloor\right).
$$
If $L>R$, the pair can be skipped. In particular, the exact number of smaller integer locations in a successful projection is $R-L+1$. Half-open intervals assign each rational boundary to one cell. The experiment bisects each interval by the mediant of its two endpoints, the comparisons in the Stern–Brocot form of the Euclidean algorithm. A complete Euclidean quotient combines consecutive comparisons in the same direction. A different convention for terminal rational endpoints requires the corresponding open or closed integer rounding. [Projection theorem](../PrimeFactors/ReciprocalPrefixPairs.lean) · [FLINT’s continued-fraction interval arithmetic](https://flintlib.org/doc/algorithms/number-theory/continued-fractions.html)

Scan the intervals for $M/x$ from right to left and those for $Mx/N$ from left to right. When two projected intervals overlap, output the intersection. Advance whichever interval ends first, advancing both if they tie. Every comparison consumes at least one interval. Distinct occupied pairs also have distinct sums of their two ordered ranks, since both ranks can only increase. Lean proves the resulting $k+l-1$ bound even for a prefiltered set of locations. Exhaustive projection still assigns an interval pair to every original $x$.

## What a negative residue check can remove

For a modulus $m$ coprime to $N$, a candidate $x\equiv a\pmod m$ requires its partner to be congruent to $Na^{-1}\pmod m$. Take the first and last eligible $x$ in one projected interval and look for an integer in this required residue class in the corresponding partner interval. If there is none, the whole lane can be rejected.

**A rejection removes at most one smaller-factor location.** If the lane contains $x$ and $x+m\le\sqrt N$, put $t=\lfloor N/(x+m)\rfloor$. Then $t\ge x$. The $m$ integers from $t+1$ to $t+m$ include a $y$ in every residue class modulo $m$. Each satisfies $xy\le x(t+m)\le(x+m)t\le N<(x+m)y$. Hence some real smaller coordinate between $x$ and $x+m$ has an integer partner in the required class. This accounts for the failure of the separate coordinate check. The existing quotient-strip method uses a stronger joint congruence on the two integer coordinates. [Rejection bound and singleton characterization](../PrimeFactors/ReciprocalPrefixPairs.lean) · [Joint congruence and quotient strips](quotient-search.md)

This bound also applies to adaptive choices of intervals, residues and moduli. In the central product bin $9U^2/16\le N\le5U^2/8$ with $U=2^{1024}$, Dusart’s published prime counts give at least $2^{1011}+1$ feasible *prime* locations for the smaller coordinate. After $R$ rejected interval-and-residue checks, at least $2^{1011}+1-R$ of those locations remain. If there were also $K$ prior weighted square labels in the project’s displacement bound, the combined lower bound is $2^{1011}+1-R-144\cdot 2^{512}K$. Feasibility here imposes bit widths and ordering. Final factor recovery still requires the exact integer product. [Combined theorem](../PrimeFactors/ReciprocalPrefixPairs.lean) · [Displacement bound](what-arbitrary-weighted-square-tests-can-exclude.md) · [Dusart, equation 6.6](https://arxiv.org/pdf/1002.0442#page=9)

## Bounded results

The experiment sets $M=2^b$ for balanced $b$-bit factors, covers $[1,2)$ on both reciprocals, uses every unit class modulo 24, and takes its data from the public product alone. The fixture names below refer to the product values in the existing five-weight comparison. Only the crossed control is in the central bin of the preceding prime-count statement. The projection and per-rejection bounds apply to both controls. [16-bit benchmark](../benchmarks/reciprocal-prefix-pairs.json) · [Control inputs](../benchmarks/weighted-crowding.json) · [Exhaustive small endpoint tests](../tests/test_reciprocal_prefix_pairs.py)

| Product | Intervals per reciprocal | Possible pairs before projection | Pairs visited and occupied | Nonempty residue lanes checked | Smaller locations removed |
| --- | ---: | ---: | ---: | ---: | ---: |
| 40,913 | 4 | 16 | 3 | 14 | 13 of 14 |
| 11,379,953,886,758,221 | 256 | 65,536 | 152 | 1,216 | 0 of 7,296,534 |
| Fresh 2,048-bit control | 256 | 65,536 | 49 | 392 | 0 of more than $2^{1019}$ |
| Crossed 2,048-bit control | 256 | 65,536 | 230 | 1,840 | 0 of more than $2^{1019}$ |

For 40,913 the surviving location came from $[3/2,5/3)$ and $[1,4/3)$. Their projection is $160\le x\le170$, containing just $163$ in residue class 19 modulo 24. Division gives $251$. Every one of this example’s 14 unit locations occupied a singleton lane, so 14 direct divisibility checks would also decide them all. Lean checks both interval endpoints, the singleton lane, both primes and their product. Run `python3 -m experiments.reciprocal_prefix_pairs 40913 --depth 2` to repeat the sweep.
