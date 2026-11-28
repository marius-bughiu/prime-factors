# Six small checks before an integer square test

**Using the product alone, six small remainder checks remove more than 99.3319% of the exact square tests** from the project's earlier search, summed over every product of two distinct 1,024-bit primes with a 2,048-bit product. For each old square test, the filtered search uses fewer than **1.5852 small lookups** on average across that population. Both bounds are unconditional. Even with this saving, the search still needs at least $2^{853}$ exact square tests on all but fewer than one input in $2^{35}$. [Square-test comparison](../PrimeFactors/SixSquareScoreWork.lean) · [Lookup costs](../PrimeFactors/SixSquareScoreLookupCost.lean) · [What still has to be searched](../PrimeFactors/SixSquareScoreVisits.lean)

## What changed in the search?

The earlier method proposes possible sums $s=p+q$ in an order chosen from the public product $N$. To test a sum, it checks whether $s^2-4N$ is an exact integer square. At the right sum this quantity equals $(p-q)^2$. The earlier order already uses the remainder modulo 25 and the location of the candidate. [Original order and its cost](using-both-the-location-and-remainder-of-a-sum.md)

For each candidate, first check whether the discriminant could be a square modulo 9, 49, 121, 169, 289 and 361, stopping on the first failure. A genuine integer square passes all six. The candidates that survive retain their original order. These are familiar quadratic-residue tests. The new bounds count their cost **through the successful test on all eligible full-size inputs**, including products where the earlier search already finished immediately. The six square-residue tables need 998 entries of one bit each, or 130 bytes if each table starts on a byte boundary. [Sieve and exact largest surviving set](../PrimeFactors/SixSquareAuxiliarySieve.lean) · [Stages and table sizes](../PrimeFactors/SixSquareLookupStages.lean)

Take the deliberately selected product 134,765,977. With ten or fewer sum progressions active, the earlier order tests 140 discriminants before finding the square that gives 8,233 and 16,369. The six checks reject 139 of them. They cost 193 small lookups and leave one exact square test. This example gave the largest absolute reduction in our 14-bit census. [Reproduce these counts](../experiments/six_square_prefix_counts.py) · [Factorization fixture](../benchmarks/cases.json)

| Bits per prime | Every eligible product | Prior exact square tests | After six checks | Small lookups |
| ---: | ---: | ---: | ---: | ---: |
| 10 | 1,718 | 3,309 | 1,719 | 12,349 |
| 12 | 19,546 | 103,850 | 19,680 | 232,521 |
| 14 | 228,713 | 4,390,120 | 239,792 | 7,272,370 |

These small census counts use the known prime sum only to locate where the search stops for measurement. Each earlier rank was checked against an independent count for its remainder classes. The 14-bit reduction was 94.54%. Short searches have a larger proportion of successful tests, which any correct filter must keep. [Census and independent rank calculation](../experiments/six_square_prefix_counts.py)

## Why the full-width bound is stronger

In each one of at most ten progressions, consecutive candidates differ by 100. The six new moduli are coprime to 100. Every block of $L=940{,}839{,}860{,}961$ successive entries in one progression visits every residue modulo $L$ once. At most $6{,}285{,}399{,}120$ entries pass all the checks. The exact worst-case fraction per complete block is $2160/323323$, about 0.668063%. The successful candidate can occur partway through a block, so Lean charges one possible incomplete block in each progression. The earlier lower bound on long searches makes that correction small in the total. [Count through an arbitrary stopping point](../PrimeFactors/ScorePrefixSieve.lean) · [Population bound for the earlier search](../PrimeFactors/WithinResidueSearchFloor.lean)

The lookup count charges the failing lookup and gives a successful candidate six lookups. Each later test is charged only to entries surviving all earlier ones. Across complete blocks, adding those six worst-case fractions costs at most $80{,}926/51{,}051$ lookups per original candidate, about 1.585199. The calculation counts the exact square tests and the small lookups separately. Converting those counts into elapsed time also requires a cost for calculating remainders, generating candidates and maintaining the order. [Proof of the per-candidate accounting](../PrimeFactors/ScorePrefixLookupWork.lean)

There is also a precise break-even test for these two operation counts. Price an exact square test at one unit. If a small check, including the remainder calculation being charged to it, costs at most $993319/1585200$ units (about 0.62662), the combined charge for the two operations strictly decreases over the population. The time for setup and candidate generation still has to be accounted for separately. [Price comparison](../PrimeFactors/SixSquareScoreLookupCost.lean)
