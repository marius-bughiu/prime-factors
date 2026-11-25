# Checking a group of factor guesses against a curve

Starting with **502,005,281,288,939** alone, we found **17,838,631 × 28,141,469**. We split the search into 9,779 intervals. Two straight lines around the curve of possible factor pairs let us discard 7,135 entire intervals. We checked 35,334 positions in the rest. Using horizontal bounds on the same intervals required 281,150 position checks. Both searches exhausted the same 613 coordinate pairs. An earlier weighted-sum method in the repository is faster on this particular product. [Checked comparison](../benchmarks/offset-coordinate-gaps.json) · [Earlier measurements](grouping-remainder-searches.md)

On each of the two 2,048-bit controls, we chose four coordinate pairs from the product. Within those four pairs the new bounds ruled out at least **99.81%** and **99.87%** of the initial offsets, respectively. Even there, more than $2^{501}$ positions on each input passed the new test. We tried three positions on each input and found neither prime. Selecting a winning coordinate pair and searching it economically remain separate problems.

## What a pair of coordinates tells us

Suppose $N=pq$ for two distinct odd primes of equal width, with $17\le p<q$. The product gives $T=\lfloor\sqrt N\rfloor$, $h=N-T^2$, and $J=\lfloor\sqrt{4h/3}\rfloor$. The earlier proof guarantees a successful test at some $1\le j\le J$ and coprime positive coordinates $(s,v)$ in an explicit search region. Write $k=sv$. At the correct coordinates, the weighted sum $S$ and the **signed difference** $z$ satisfy

$$
S=j+2Tk=ps^2+qv^2,\qquad z=ps^2-qv^2,\qquad z^2=S^2-4Nk^2.
$$

For each guessed $(s,v)$ we can compute the possible remainders of $z$ without either prime. Choose $e$ equal to zero modulo $v^2$ and one modulo $s^2$. Such an $e$ exists because $s,v$ are coprime. Put $C=1-2e$. Writing $p=1+2x$ and $q=1+2y$ gives

$$
j\equiv s+v\pmod 2,\qquad
z\equiv s^2-v^2+C(S-s^2-v^2)\pmod {4k^2}.
$$

Indeed $C$ acts as $+1$ on the term $s^2x$ and as $-1$ on $v^2y$ modulo $2k^2$. Lean proves the congruence more generally when residues of the two factors modulo any $m$ are specified. Here both residues modulo two follow from the input assumptions. The search starts at the first offset of the required parity with $S^2\ge4Nk^2$. [Offset and coordinate guarantee](factoring-the-offset-multiplier.md) · [Signed congruence and coverage proof](../PrimeFactors/OffsetCoordinateGaps.lean)

For example, take $N=117449$, $s=4$, $v=3$. At offset $j=17$ the trace is 8,225 and the signed difference must be 575 modulo 576. The discriminant is 1, so the signed difference is $-1$. This gives $(8225-1)/(2\cdot4^2)=257$ and $(8225+1)/(2\cdot3^2)=457$. Keeping only the positive square root as the signed remainder would lose this solution. [Checked negative-gap example](../PrimeFactors/OffsetCoordinateGaps.lean)

## Counting a whole interval

Set $P=4Nk^2$. In one interval let the trace run from $A$ to $A+d$, and let $x=S-A$. The horizontal test puts $|z|$ between the ceiling square root at the left and the floor square root at the right. To follow the curve, take $l=\lfloor\sqrt{A^2-P}\rfloor$ and $r=\lfloor\sqrt{(A+d)^2-P}\rfloor$. For $d>0$ reduce $(r-l)/d$ to $a/b$ with $b>0$. Since $(l+d)^2\le (A+d)^2-P$, we have $a\ge b$. Every possible integer root satisfies

$$
b l\ \le\ b|z|-a x\ \le\ aA-\left\lceil\sqrt{(a^2-b^2)P}\right\rceil .
$$

For the lower bound, subtract the square of the chord from the curve's squared height. The difference is a concave quadratic because the chord slope is at least one. Its endpoint values are nonnegative, as the two heights were rounded down. For the upper bound use $(aS-b|z|)^2-(a^2-b^2)P=(bS-a|z|)^2$ and $aS\ge b|z|$. The bounds also work when either endpoint is an exact square. A singleton uses its horizontal interval. [Integer chord and support theorems](../PrimeFactors/OffsetCoordinateGaps.lean)

For either choice of sign, the expression in the middle has a known affine remainder modulo $4bk^2$ as $j$ increases by two. A difference of two Euclidean floor sums counts its visits to an interval of remainders. We split an interval that wraps around zero and combine overlapping intervals for a single sign. The larger of the two sign counts is a lower bound on the number of distinct candidate positions. Their sum, capped by the interval length, is an upper bound. When reporting candidates we test a position only once. If at most two possible signed roots fit in its band, we square those integers directly. Otherwise we take an integer square root. Counts of endpoint roots, explicit squarings, fallback roots, and Euclidean steps are recorded separately. [Counting and search implementation](../experiments/offset_coordinate_gaps.py) · [Floor-sum routines](../experiments/modular_hyperbola.py)

We place more intervals near the first possible square, where the curve bends most. For $n$ eligible offsets and $m=\min(n,\text{requested parts})$, the boundaries have indices $i+\lfloor(n-m)i^2/m^2\rfloor$ for $0\le i\le m$. This gives positive lengths and covers every offset exactly once. The comparison uses the same boundaries in both modes. Counting requires a constant number of floor sums per interval. Listing the survivors and checking them costs additional work. Interval factoring via rational approximation has a long history. Hiary's algorithm tests short divisor intervals with a quadratic. The present inequalities concern the two weighted factors at prescribed offset coordinates. We have no improved general complexity bound for integer factorization. [Hiary's algorithm](https://arxiv.org/abs/1408.2608)

## What the checks found

| Complete schedule, 16 intervals requested per coordinate pair | Horizontal | Chord |
| --- | ---: | ---: |
| Eight earlier small products, distinct positions tested | 7,256 | 1,886 |
| Successful positions, giving eight prime pairs | 9 | 9 |
| Median total time on the eight products | 0.030 s | 0.023 s |
| 49-bit product, initially eligible offsets by coordinate | 731,911 | 731,911 |
| Distinct positions tested | 281,150 | 35,334 |
| Roots for chart and interval bounds | 20,171 | 29,810 |
| Explicit candidate squarings | 165,090 | 18,588 |
| Fallback square roots at individual candidates | 71,701 | 10,133 |
| Euclidean steps for counting and reporting | 1,442,408 | 503,362 |
| Median complete search time | 0.918 s | 0.284 s |

Times are local medians of five runs in alternating order, with prime certification separate. The 49-bit example was the first product in a previously published series. On 117,449 the chord search needed seven position checks for $257\times457$. Lean verifies the product and both primes in every complete benchmark row. The counting implementation reuses this project's MIT-licensed floor-sum routines. [Eight comparison inputs](../research/quartic-lane-holdout.json) · [49-bit series](../research/midpoint-weight-holdout.json) · [Frozen checks](../benchmarks/offset-coordinate-gaps.json) · [Project license](../LICENSE)

For each full-size input, the four trial values of $v$ come from the first four fifths of the public limit on $v$. For $s$ the rule takes the midpoint of its allowed range and moves down to a coprime value. These choices used only $N$. With 64 intervals per coordinate pair, the base-two logarithms of the retained position count lie between 502.346 and 503.347 on the fresh input and between 501.290 and 502.291 on the crossed input (outward rounding). These are counts before the remaining gcd and exact-square checks, restricted to the four pairs. All 256 intervals on each input remained nonempty.

We also counted what happens **if the winning coordinates are supplied** from the previously published factors. The upper bounds there were 0.0374% and 1.124% of the initial offsets, respectively, still exceeding $2^{499}$ in both examples. This retrospective calculation supplies no rule to choose those coordinates from $N$. A separate result gives just how tightly supplied coordinates can constrain a factor itself. [Known-coordinate diagnostic](one-or-two-winning-tests.md) · [Factor intervals and limits of the size test](short-factor-projections.md)

~~~sh
python3 -m experiments.offset_coordinate_gaps 502005281288939 --all-vectors --max-vectors 1000 --parts 16 --max-tests 500000
python3 -m experiments.offset_coordinate_gaps 502005281288939 --all-vectors --max-vectors 1000 --parts 16 --max-tests 500000 --horizontal
~~~
