# When trying two remainders first saves square tests

For **more than 24.9%** of products of two distinct 1,024-bit primes with a 2,048-bit product, we can prove that a change in search order saves **at least 70% of the exact square tests**. Every product counted in that guarantee still takes **at least $2^{894}$ tests** in the faster order. The comparison is between two elementary searches through possible factor sums. It gives no practical way to split a typical 2,048-bit number. [Population and work bounds](../PrimeFactors/FavoredSumWork.lean)

## What changes in the search?

Given $N$, suppose the unknown primes are $p$ and $q$. Their sum $s$ satisfies $s^2-4N=(q-p)^2$. We can test a proposed $s$ by taking an integer square root. The input and the known bit widths give a lower and upper bound for $s$. Both searches use these bounds and discard the same candidates using arithmetic modulo 4 and 25. Both count the successful test. [Range and exact-square test](../PrimeFactors/FactorSumPrefixCost.lean)

The first search tests the surviving sums in increasing order. The second gives priority to those with $s^2-4N$ divisible by five. It tries that whole group in increasing order, then tries every remaining survivor in increasing order. Which group a candidate belongs to can be calculated from $N$ and the candidate. For products square and nonzero modulo five, each 100 consecutive integers contain seven surviving sums, two of them in the priority group. [Exact count in every block](../PrimeFactors/PeriodicSumRank.lean)

For example, $7{,}253{,}249=2{,}053\times3{,}533$. The public range starts at 5,387. The true sum is 5,586. Checking every survivor in order takes **14 tests**. The priority search tests **5,414, 5,486, 5,514, 5,586** and succeeds on its fourth test. The last discriminant is $1{,}480^2$, giving both primes. [Checked prefixes](../PrimeFactors/FactorSumPrefixCost.lean)

## Which products benefit?

The true sum belongs to the priority group precisely when the two prime factors are equal modulo five, since its discriminant is $(q-p)^2$. When the true sum is far above the start of the search, the unfinished last group of 100 integers changes the relative cost only slightly. At distance 10,000 or more, the priority search uses at most 30% as many square tests on a priority-group hit. [Per-input proof](../PrimeFactors/FactorSumPrefixCost.lean)

Give equal weight to each eligible pair of primes, with the smaller prime first. More than 24.9% both meet the remainder condition and have a sum at least $2^{900}$ above the start. Among the products congruent to 1 modulo 25, the share meeting both conditions exceeds 49.9%. The count uses the published unconditional prime-count estimate of Bennett, Martin, O’Bryant and Rechnitzer as an explicit Lean hypothesis. Lean verifies the deduction, including the exclusion of pairs whose sums lie too close to the start. The $2^{894}$ lower bound follows by counting the two tests in each complete block of 100 before the true sum. [All product remainders](../PrimeFactors/FullPopulationFavoredSums.lean) · [Products congruent to one](../PrimeFactors/FullRangeLongSumPrefix.lean) · [Unconditional source, Theorem 1.3](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5)

These percentages count the products with guaranteed savings. When the true sum belongs to the second group, the priority search first pays for candidates above it. An average over all inputs must count those extra tests as well. The unit of work here is an exact square test. The comparison excludes the cost of generating candidates and makes no elapsed-time prediction.

## What if we reorder only one block at a time?

A separate search prioritizes the same residues within each consecutive block of 100 integers, then moves on. This limits how much the stopping position can change. Even on a clipped final block the target can move at most five places earlier or two places later. Both extremes occur. [Sharp bounds and three examples](../PrimeFactors/PeriodicSumRank.lean)

| Product | Ascending tests | Priority within each block |
| ---: | ---: | ---: |
| 7,253,249 | 14 | 9 |
| 7,688,801 | 17 | 19 |
| 6,296,551 | 8 | 8 |

We checked both block orders by testing actual squares for all 17,945 eligible pairs of distinct 9-, 10- or 12-bit primes. At larger widths we used the known true sums to calculate stopping positions. Among 648,855 eligible 15-bit pairs, the count fell from 21,408,323 to 21,078,190, about 1.54%. On 229,628 of those pairs, block priority reached the answer later. These sample populations require a square unit product modulo 25 and equal prime bit widths. They include products of either possible bit length. [Reproduce the comparisons](../experiments/toy_period_sum_order.py)
