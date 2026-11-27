# Which signed curve should we search first?

Searching the cheapest of three guaranteed curves first reduced the number of blocks needed to find a factor by **29.7%** across twelve products of 16-bit primes and **14.3%** across twelve products of 20-bit primes. All 24 factorizations have Lean-checked certificates. On one 2,048-bit input we could also replace the original three curves with a cheaper set and reduce the cost of exhausting them by **29.1%**. The reduced set still costs about $2^{684.73}$ blocks. None of the full-size trials found a factor in 64 blocks. [Measurements and certificate hashes](../research/signed-curve-order.json)

## What choices does the product permit?

Suppose $N=pq$ for distinct primes above three. For each signed target $D$ among $-1,2,-2,3,-3,6,-6$, the product gives a Jacobi sign. Keep the targets with sign $+1$. For each of these the two prime factors agree about whether $D$ has a square root. When both say yes, the equation $x^2-Dy^2=mN$ with its single public multiplier has two inequivalent modular roots represented in the finite chart. Finding them gives a proper factor by gcd. This is the quadratic-form method of D. H. and Emma Lehmer. [Original paper, pp. 625–627](https://doi.org/10.1090/S0025-5718-1974-0342458-5) · [Reduced chart and implementation](scanning-signed-norm-arcs.md)

Number the seven targets from 1 to 7 in the order above. The three bits of a number record the exponents of $-1,2,3$. If two eligible targets with masks $a,b$ both lack square roots at $p$, their product has one at $p$. The same holds at $q$. Removing square factors from the product gives the third mask $a\mathbin{\mathrm{xor}}b$. Thus at least one target in the triple is rootable. Such a triple is called a *line* in the seven-point binary projective plane.

For $N\equiv1\pmod{24}$ every target is eligible, giving seven lines to choose from. Each other possible product residue gives just one line. Lean checks that a selection guarantees a root for every possible hidden sign row **if and only if it contains a line**. Consequently the cheapest eligible line minimizes total exhaustive cost amongst all selections whose guarantee uses only these signs, for *any* nonnegative additive per-curve price. This guarantee concerns exhausting a set of curves. A factor can appear anywhere inside one of them. [SignedCurveSchedule.eligible_line, complete_cover, contained_cost and listed_split](../PrimeFactors/SignedCurveSchedule.lean)

## A blind comparison to the first factor

The four schedules were fixed before drawing products. The original searches the first three eligible targets in published repository order. The sorted schedule searches the same targets by ascending exact block count. The cheapest-line schedule prices every eligible line, chooses the least total cost and searches it in the same sorted order. Ties use the numerical masks. The cyclic schedule uses that same cheapest line and advances one block per active curve in turn. If a chosen curve finds a factor on its own $t$-th block, the cyclic schedule finds a factor within $3t$ charged blocks. Its guarantee applies only to the curves it selects. [Search and scheduling code](../experiments/signed_curve_order.py)

Every method uses the same integer arc implementation and reduced charts. Computing a curve's price needs only its public endpoints and block widths. A chart containing $M$ positive positions and using width $W$ costs exactly $\lceil M/W\rceil$ blocks. The recorded block counts charge the complete winning block. CPU measurements include Jacobi signs, pricing, axis tests, search, root reconstruction and gcd. Certificate generation and a separate per-curve replay fall outside those timings.

The main set takes the first twelve distinct-prime products at each width from fresh, fixed SHAKE-256 streams. A separate, predeclared sample takes the first six products at each width with $N\equiv1\pmod{24}$ from different streams. This allows a comparison where all seven lines really are available. Search receives only $N$. The archived results record which curve split, the decimal factors, and a checked Lean certificate hash for each of the 36 products. [Prime draw](../experiments/affine_radix_holdout.py) · [Measurements](../research/signed-curve-order.json)

| Sample | Original blocks | Sorted blocks | Cheapest line blocks | Cyclic blocks |
|---|---:|---:|---:|---:|
| Main, 12 × 16-bit primes | 39,231 | 27,590 | 29,137 | 46,542 |
| Main, 12 × 20-bit primes | 273,290 | 234,226 | 244,534 | 318,275 |
| $N\equiv1$, 6 × 16-bit primes | 17,950 | 12,617 | 8,030 | 18,447 |
| $N\equiv1$, 6 × 20-bit primes | 157,883 | 131,381 | 87,096 | 154,475 |

The same comparison in process CPU milliseconds on arm64 with Python 3.9.6 follows. Each entry adds the per-product median from two complete runs to the first factor.

| Sample | Original | Sorted | Cheapest line | Cyclic |
|---|---:|---:|---:|---:|
| Main, 16-bit | 142 | 102 | 106 | 172 |
| Main, 20-bit | 1,142 | 974 | 1,015 | 1,348 |
| $N\equiv1$, 16-bit | 63 | 45 | 29 | 66 |
| $N\equiv1$, 20-bit | 682 | 567 | 375 | 670 |

Only one product at each width in the main sample allowed a change of line. In both cases the cheaper line took more blocks to its first factor than sorting the original line. On the separate $N\equiv1$ sample the cheaper line typically helped, beating the sorted original on five of six 16-bit and four of six 20-bit products. Reordering alone caused both a large win and a large loss. It recovered $1{,}930{,}450{,}843=33{,}797\times57{,}119$ in 34 blocks against 6,215 originally, but needed 6,850 against 790 for $2{,}333{,}613{,}547=38{,}867\times60{,}041$.

## Two public 2,048-bit inputs

The fresh input has $N\equiv7\pmod{24}$, so all schedules have the same complete cost of about $2^{685.185}$ blocks. The crossed input has $N\equiv1\pmod{24}$. Its original line $\{-1,2,-2\}$ costs $2^{685.225}$ blocks and the cheapest line $\{2,3,6\}$ costs $2^{684.730}$. Every schedule spent 64 blocks on each input and returned an unresolved cofactor. The full costs come from exact integer endpoint arithmetic. The actual searches stopped after the stated prefix.

The same price rule can be used by a direct row scanner. Counting positive chart-coordinate rows in place of arc blocks picks $\{2,3,6\}$ on the crossed input. This changes its complete row count from about $2^{1025.322}$ to $2^{1024.347}$, a 49.1% reduction. On the fresh input the count stays at about $2^{1025.312}$. These counts exclude the finite axis checks. [Public inputs and exact per-curve row and block counts](../research/signed-curve-order.json)

Run `python3 -m experiments.signed_curve_order --output build/signed-curve-order.json` to regenerate the panel. Each schedule runs twice per product in alternating order with a cold residue table. Each case records the median process CPU time, and the summary adds those medians. An independent replay using the original per-curve iterator checks the exact block of every first split. The implementation reuses this repository's MIT-licensed integer arcs, prime draw and certificate checker. [Source](../experiments/signed_curve_order.py) · [Bounded regression tests](../tests/test_signed_curve_order.py) · [License](../LICENSE)
