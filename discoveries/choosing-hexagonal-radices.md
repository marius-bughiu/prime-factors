# Choosing a radix by the number of slopes

On the 82-bit product $3043806426885490749164321$, a smaller admissible radix and a count of its slopes reduced the complete CRT search from **3.65 to 2.71 seconds**. Simply rounding to the first admissible smooth radix increased it to 7.51 seconds. All three searches found $1688035255729\times1803165198449$. On the 2,048-bit control the selected radix still had a 584-bit number of slopes and required a list of $2^{47}$ entries just to process the first one. [Hexagonal weight theorem](hexagonal-weight-bound.md) · [CRT search](weight-slope-batches.md) · [Complete measurements](../research/hex-weight-holdout.json)

## Which radices are admissible?

The input is $N=pq$ with distinct odd primes $p<q\le2p$. The midpoint $h=(p+q)/2$ and signed half-gap $d=(q-p)/2$ satisfy $h^2-d^2=N$. Let $h_0=\lceil\sqrt N\rceil$, $h_1=\lfloor\sqrt{9N/8}\rfloor$, $H=h_1-h_0$, $D=\lfloor\sqrt{N/8}\rfloor$ and $G=2D$. The rectangle uses $h_0\le h\le h_1$ and $|d|\le D$. The tighter bound $|d|\le D-3(h_1-h)$ also couples the two coordinates. It reduces the sufficient threshold for a single weighted sum per remainder pair from $R^3>4HG$ to
$$
(G+3H)R^3>4HG^2 .
$$
When $H=0$, the search tests the single midpoint directly.

For each slope the experiment checks four candidate weights from the old Gauss-reduced basis and chooses the smallest hexagonal width. For the comparison with exact curved endpoints it then intersects the resulting interval with the true range of the weighted sum on the continuous balanced hyperbola. The rectangle baseline gets the same curved-endpoint calculation. Every method uses the same CRT reporting engine and ordinary integer-square test. [Proof of the four-direction rule](../PrimeFactors/HexagonalWeights.lean) · [Weight implementation](../experiments/hex_weight_interval.py) · [Curved endpoints](curved-weight-limits.md)

## Why a smaller radix can cost more

The number of slopes at a coprime radix is $S(R)=\varphi(R)/K(R)$, where $K(R)$ is the number of square roots of one modulo $R$. Both quantities can be computed from the factorization of the **public radix**. For an odd prime power $p^e$, its factor in $S$ is $p^{e-1}(p-1)/2$. For $2^e$, divide its totient by one, two or four according as $e=1$, $e=2$ or $e\ge3$. CRT multiplies these local factors. The swap-orbit convention visits every one of these slopes. [Exact slope count](../PrimeFactors/CanonicalWeightSlopes.lean)

We tried three choices. The rectangle baseline and the first hexagonal choice each round their own target using the repository's existing smooth-radix rule. The third choice takes both rounded endpoints, uses their gcd as a stride, and compares the intervening multiples coprime to $N$. If there are more than 64 choices before the coprimality test, it samples at most 64 evenly spaced indices including both endpoints. It chooses the smallest slope count, breaking ties toward the smaller radix. Either endpoint exceeds the hexagonal threshold, so every intervening choice does too. The old radix always participates. Hence the selected slope count is **at most** the old count; the order and size of individual CRT lists can still change. The code charges the trial divisions for counting slopes to the search. [Radix selection](../experiments/hex_weight_interval.py) · [Search engine](../experiments/midpoint_slope_batches.py)

## Complete comparisons

For the 82-bit input the three radices were 80,660,580, 75,044,970 and 75,555,480 respectively. Ranking the 12 candidates permitted by both thresholds more than halved the original 56,160 slopes. Times are medians of two opposite-order runs on arm64 macOS 27.0.1 with CPython 3.9.6. Times exclude Lean verification.

| Selection, all with curved endpoints | Slopes | Half-list entries | Square tests | Seconds |
| --- | ---: | ---: | ---: | ---: |
| Rectangle threshold | 56,160 | 1,241,556 | 3,229,018 | 3.653 |
| First hexagonal radix | 211,680 | 2,496,914 | 3,744,091 | 7.513 |
| Hexagonal candidates ranked by slope count | 25,920 | 763,384 | 3,142,652 | 2.710 |

We developed the slope-count choice after inspecting rounded radix sizes on the previously frozen eight 49–50-bit products. We then fixed the same choice for a second sample generated with ASCII seed `hex-radix-slope-holdout-v1`. Each sample consists of eight distinct-prime pairs drawn from two 25-bit streams. The table sums the per-input medians of five rotating-order runs. All 16 products were recovered. The stored measurements include all six combinations of interval geometry, radix strategy and use of curved endpoints. [Comparison script](../experiments/hex_weight_holdout.py) · [Timings, work and factors](../research/hex-weight-holdout.json)

| Sample, all with curved endpoints | Rectangle slopes / seconds | First hexagonal slopes / seconds | Slope-ranked slopes / seconds |
| --- | ---: | ---: | ---: |
| Previously frozen eight | 2,280 / 0.05421 | 3,360 / 0.06986 | 1,920 / 0.04694 |
| New independent eight | 2,460 / 0.05574 | 3,210 / 0.06681 | 1,950 / 0.04635 |

The selected slope count fell on two inputs in each sample and stayed equal on the other six. On the frozen sample, one of the eight curved searches became slower despite the guarantee on slope counts. On the new sample all eight were faster in this comparison. Without the final curved-endpoint intersection, slope ranking still reduced the total times from 0.05306 to 0.04588 seconds and from 0.05457 to 0.04466 seconds respectively. These measurements compare variants of one deterministic search.

For the same crossed 2,048-bit input, the rectangle, first hexagonal and slope-ranked choices gave slope counts of 586, 585 and 584 bits. Their first slopes requested half-lists of $2^{46}$, $2^{46}$ and $2^{47}$ entries. All three stopped at the 65,536-entry limit before searching a single slope. A separate search later recovered the crossed primes by testing remainder 1. [Crossed factorization](testing-one-factor-remainder.md) · [Capped fixture and Lean-replayed smaller examples](../benchmarks/midpoint-slope-batches.json)
