# How often do 34 square roots find the factors?

The search that checks two different factor ranges succeeded on **48.69%** of eligible products of two 16-bit primes. With two 26-bit primes, its success rate fell to **1.515%**. At 26 bits it still found over twice as many *additional* products as continuing ordinary Fermat search after their common start. These are exact counts for a specified range of products and a fixed search budget. [Full counts and work measurements](../research/weighted-partner-counts.json) · [Search schedules](using-two-factor-ranges-after-sixteen-tests.md)

| Bits per prime | Eligible products | Split in common start | Extra from ordinary continuation | Extra from two new ranges | Total split by two-range search |
|---:|---:|---:|---:|---:|---:|
| 16 | 592,048 | 145,803 | 62,262 | 142,452 | 48.69% |
| 20 | 96,713,943 | 5,939,001 | 2,575,671 | 5,818,060 | 12.16% |
| 24 | 17,115,589,103 | 259,706,431 | 113,223,856 | 258,705,622 | 3.029% |
| 26 | 232,778,357,093 | 1,771,986,096 | 772,972,217 | 1,754,407,933 | 1.515% |

At 26 bits, ordinary continuation was the only one of the three continuations to split 772,972,217 products. The two-range continuation was the only one to split another 1,029,008,511. Choosing a continuation changes which products the search can recover. [Joint outcomes for all three searches](../research/weighted-partner-counts.json)

The product itself can guide this choice. A follow-up kept the same two ranges and the same budget, choosing the split of fifteen tests from the remainder of the input modulo 24. A formula for interval length fixed the rule before the outcomes were counted. At 26 bits it yielded a net **20,441,262** more successes, moving the overall rate from 1.5149% to 1.5237%. Some individual products were lost as others were gained. [Allocation rule, gains and losses](allocating-weighted-tests-from-the-product-remainder.md)

At each width put $U=2^{\mathrm{bits}}$. The table includes every pair of distinct primes $U/2\le p<q<U$ with $9U^2/16\le pq\le5U^2/8$. Each search starts with 16 admissible ordinary sums. Continuing ordinary search spends its remaining budget on 17 more ordinary sums. The two-range search spends it on seven labels for $3p+2q$ and eight for $7p+5q$, including the costs of starting those two ranges. At every width both searches get 34 integer square roots in total. [Method and budget](using-two-factor-ranges-after-sixteen-tests.md)

## Counting without running billions of factorizations

To evaluate the method, we sieve the primes and fix a smaller prime $p$. At a given remainder of $q$ modulo 24, a possible true sum $S=Ap+Bq$ has a known remainder. Let $D$ be the distance back from $S$ to the $H$-th preceding label admitted by the search. Periodicity modulo 24 makes $D$ fixed for the whole row. The search reaches $S$ among its first $H$ admitted labels precisely when the preceding label lies below the starting square root. In the ranges used here $S-D$ is positive. Squaring and completing the square gives

$$\big(Bq-(Ap+D)\big)^2<4ApD.$$

Thus a single integer square root of $4ApD-1$ gives the inclusive endpoints for an interval of possible $q$. The subtraction of one retains the strict inequality at perfect-square boundaries. We check the factor assignments $AB=k$ that the search admits, combine their intervals, restrict them to the product range and count the primes inside by binary search in sorted residue classes. Overlaps count only once. [Counting code](../experiments/weighted_partner_counts.py) · [Lean proof of the reverse rank and interval criterion](../PrimeFactors/WeightedPartnerIntervals.lean)

The 26-bit census took about 43 seconds of counting after sieving in one local run. It performed 34,737,530 interval square roots to count 232,778,357,093 products. At 16 bits all outcomes agree with direct product-only searches over the entire population. An independent per-pair calculation also reproduced all five headline counts at 18 bits, including 887,482 additional two-range splits in 7,466,743 products. Boundary and sampled-product tests check the larger widths. [Reproducible results](../research/weighted-partner-counts.json) · [Boundary tests](../tests/test_weighted_partner_counts.py)

The census starts with known lists of primes. For factoring one supplied product, the smaller prime is unknown. Enumerating every 1,024-bit smaller prime is impractical, and the finite table gives no success percentage at 1,024 bits. The separate full-size proof bounds the range reached by these square tests. [Full-size population bound](sharing-square-tests-across-factor-ranges.md#how-often-can-this-approach-find-the-actual-prime)
