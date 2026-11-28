# Which possible divisors do six sums rule out?

For 12,707, take the supplied interval from 91 to 99. There are exactly four integer points between the tangent and chord that enclose the curve $xy=12{,}707$ there. Their first coordinates are 96, 97, 98 and 99. Six sums computed over the strip leave **97 as the only possible divisor**. The second prime is 131. This example answers a local question. Choosing an interval that contains the factor still costs work. [Lean proof of the complete strip and its unique survivor](../PrimeFactors/QuotientStripLocalization.lean) · [Prime certificate fixture](../benchmarks/cases.json)

## Why can a sum rule out an individual coordinate?

At every strip point record its first coordinate $x$ and its error $e=xy-N$. A factor point has error zero. Let $G$ be the sum of the outer products of the column vectors $(1,x,e)$. Its six independent entries are the count and the sums of $x,e,x^2,xe,e^2$. Integer floor-sum recurrences compute them from the product and the strip endpoints. Removing a true row leaves another Gram matrix, whose determinant must be nonnegative. For a candidate coordinate $k$, the row to remove is $(1,k,0)$. The resulting determinant is quadratic in $k$. Completing the square and rounding the endpoints gives an integer interval. The proof includes the zero-variance case and allows repeated coordinates. Related work on empirical Christoffel functions studies how moment matrices constrain the support of finite distributions. [Six-moment inequality and rounding](../PrimeFactors/QuotientStripLocalization.lean) · [Existing floor sums](../experiments/quotient_search.py) · [Lasserre and Pauwels](https://arxiv.org/abs/1701.02886)

There is a cheaper source of moments. The existing collinearity test already computes the count and five ordinary sums of $x,y,x^2,xy,y^2$. At a true point we may substitute $y=N/k$ into the residual determinant and multiply by $k^2$. This yields an integer quartic in $k$. Its accepted positions can have a gap. For 11,286,761 on the block 3,006–3,035, the separate coordinate bounds keep 3,010–3,035. The quartic with those bounds keeps 3,010–3,013 and 3,017–3,033. The actual factor 3,001 lies in an earlier block. A second control projects the same points onto an integer linear form chosen to cancel its covariance with $x$. The allowed range of this form gives two quadratic inequalities on $k$. [Quartic identity and linear projection](../PrimeFactors/QuotientStripHyperbola.lean) · [Independent checks at every position](../experiments/quotient_strip_localization.py)

## How much work survived an actual first hit?

The first group consists of 99 products chosen with the second prime near five quarters of the first. The holdout consists of 64 distinct pairs of different 10-bit primes selected without conditioning on their ratio. The search receives only the product. Each method visits the same blocks in ascending order, solves strips with at most three points by error moments, and handles collinear points by intersecting a line with $xy=N$. Remaining candidates undergo ordinary odd trial division. The table counts all divisibility tests through the first returned factor, including tests shared by the methods. Each method found all 163 factors. [Cohort definitions, full scans and stopping-point counters](../benchmarks/quotient-strip-localization.json)

| Terminal rule | Divisions to first, 99 selected | Divisions to first, 64 holdout | Holdout floor-moment states to first |
|---|---:|---:|---:|
| Direct odd trial over the balanced interval | 33,216 | 4,252 | 0 |
| Scan after the existing error-sum test | 27,696 | 3,385 | 103,561 |
| Separate coordinate bounds | 23,928 | 2,752 | 57,265 |
| Coordinate bounds and linear projection | 22,537 | 2,573 | 57,265 |
| Coordinate bounds and ordinary quartic | 21,767 | 2,499 | 57,265 |
| Joint coordinate and product-error bound | 21,552 | 2,488 | 103,561 |

The quartic required 14,136 polynomial sign evaluations to reach the 64 holdout factors. The joint error bound used 782 square roots and 1,564 endpoint divisions in addition to its moment calculations. Fewer divisibility tests alone do not establish a wall-clock gain. Doubling the block width exposed a limit. Across 1,589 eligible strips with at least 17 points, the error bound removed just 54 of 101,720 positions. All 99 strips containing the smaller factor in that group kept their full original interval. [Detailed work by block occupancy](../benchmarks/quotient-strip-localization.json)

## What does integer variance add?

For $h$ integer readings with sum $S$ and sum of squares $T$, the variance numerator $hT-S^2$ is at least $r(h-r)$, where $r=S\bmod h$. Applying this after a hypothetical row deletion can rule out a coordinate even when the real determinant is positive. Lean proves that for $1\le h\le7$, nonnegative variance and the parity of the two moments already imply this bound. [Discrete variance and small-population limit](../PrimeFactors/QuotientStripIntegerVariance.lean)

For $3{,}574{,}327=1567\cdot2281$, the supplied interval 1,678–1,710 contains eleven strip points. Removing a hypothetical zero-error row at the prime 1,709 leaves a positive covariance determinant of 4,580. Projecting to $39x+e$ gives variance numerator 4 where integer readings require at least 24. This excludes a false endpoint. The true smaller prime 1,567 lies outside this strip. [Checked factorization, complete point set and exclusion](../PrimeFactors/QuotientStripIntegerVariance.lean)

The short-interval chord calculation also works without collecting any moments. [Covering each factor interval with at most five lines](covering-a-factor-interval-with-five-lines.md)
