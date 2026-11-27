# Which products does skipping impossible square tests add?

We factored a second specially constructed 2,048-bit number from its product alone. The revised search found both primes on square test **1,569,459**. With the same budget of **2,097,152** tests, the earlier search missed them. Lean checked the primes, their product, the exact successful test index and the earlier search's miss. On the two full-size comparison products both searches used their entire budgets and found no factor. [Decimal inputs and expected outcomes](../benchmarks/equal-six-budget.json) · [Certificate generator](../scripts/equal_six_budget_benchmark.py)

| Product | Budget for each search | All odd labels | Labels 1 and 5 modulo 6 |
|---|---:|---:|---:|
| Earlier constructed pair | 10,176 | Missed | Split on 10,176 |
| Same pair with a larger budget | 15,264 | Split on 15,264 | Split on 10,176 |
| New constructed pair | 2,097,152 | Missed | Split on 1,569,459 |
| Fresh comparison | 2,097,152 | Missed | Missed |
| Crossed comparison | 2,097,152 | Missed | Missed |

Both methods start at the ceiling of $\sqrt{24N}$. They look for an integer $S$ for which $S^2-24N$ is square, then take a gcd. A label divisible by three cannot give a square when $N$ is coprime to six. At any fixed number of square tests, skipping these labels preserves **every** split the earlier search would have found. The two constructed examples prove that the set of 2,048-bit inputs recovered actually grows at each of the two budgets in the table. None of these claims needs a prime-distribution hypothesis. [Residue proof](../PrimeFactors/SixTraceResidues.lean) · [Equal-budget inclusion and strictness from a witness](../PrimeFactors/SixTraceBudget.lean)

## Why the earlier search really misses

For two distinct 1,024-bit primes $p<q$ we have $q<2p$. Any proper split at multiplier six assigns the two multipliers in one of four ways. The smallest possible successful label is exactly $S=3p+2q$. The other possibilities are $p+6q$, $2p+3q$ and $6p+q$, all larger. At $3p+2q$ the gcd does return a prime. This determines both searches' first successful test if the factors are known for analysis. The searches themselves receive just $N$. [Minimum label and exact ranks](../PrimeFactors/SixTraceBudget.lean)

The new example was generated before we ran either search. We chose the smaller prime on a fixed grid near $161\cdot2^{1024}/256$. With $y=3p/2$, we took the first certifiable prime on the grid between $y+2900\sqrt y$ and $y+3530\sqrt y$, rounding the endpoints inward. The generator examined 180 candidates for the smaller prime and 164 for the larger one. On this product the winning label is 4,708,375 above the first integer in the search. The odd-label method reaches it on test 2,354,188, beyond the budget. Choosing this interval deliberately tests the prediction that the methods will differ. [Reproducible construction](../experiments/displaced_prime_partners.py)

## How many such products exist?

Let $U=2^{1024}$. For each prime $p$ between $79U/128$ and $82U/128$, a prime-gap estimate under RH guarantees at least one prime $q$ in the displaced interval above. The excess of the successful label over $\sqrt{24pq}$ lies strictly above 4,199,202 and at most 6,230,450. This puts it beyond the earlier search and inside the revised search at the same $2^{21}$ tests. Distinct choices of the smaller prime give distinct products. [Displacement proof](../PrimeFactors/DisplacedPrimePartners.lean) · [Search bounds](../PrimeFactors/DisplacedTraceSchedules.lean) · [Carneiro, Milinovich and Soundararajan, Theorem 5](https://arxiv.org/pdf/1708.04122#page=5)

The resulting lower bound is **more than $2^{1009}$ additional distinct 2,048-bit products**. To count the eligible smaller primes, put $a=79U/128$ and $b=82U/128$. The inequalities $709<\log a\le\log b<710$ and Rosser and Schoenfeld's bounds on prime counts give $\pi(a)\le2a/1415$ and $\pi(b)\ge2b/1419$. Lean takes those two endpoint bounds and the prime-gap estimate as explicit premises. It proves the count for the difference of the actual searches' success sets. [Product-count theorem](../PrimeFactors/DisplacedTraceSchedules.lean) · [Counting distinct inputs](../PrimeFactors/SixTraceNewProducts.lean) · [Rosser and Schoenfeld, Theorem 2](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6)

The absolute chance remains tiny. With this budget, even the filtered search stays inside the first $2^{32}$ integer labels at multiplier six. The project's existing upper bound for that larger search is less than one success in $2^{469}$ for uniform distinct 1,024-bit primes conditioned on a 2,048-bit product. Both the large number of additional successes and the small overall fraction can hold because the population is enormous. [Population and upper bound](sharing-square-tests-across-factor-ranges.md#how-often-can-this-approach-find-the-actual-prime)
