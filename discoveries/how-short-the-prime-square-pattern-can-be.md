# How short can the repeating prime-square pattern be?

On the fresh 2,048-bit comparison, the list for all seven prime-square tests fits in **90,720 offsets**. A direct list for the original joint period would contain 29,331,862,560. Both lists describe exactly the same sums at every position. On the crossed product the shorter list needs **8,279,040 offsets**. The lists repeat throughout the much wider factor-sum interval, so reducing their size saves setup and storage. Each product still has at least $2^{1006}$ candidates overall. [Period and count proofs](../PrimeFactors/CompressedPrimeSquareWheel.lean) · [Candidate counts throughout the interval](when-a-prime-square-rules-out-a-sum.md)

| Published product | Smallest period, in consecutive integer sums | Accepted offsets in that period | Amount of repetition eliminated |
| --- | ---: | ---: | ---: |
| Fresh | 290,990,700 | 90,720 | 323,323× |
| Crossed | 38,701,763,100 | 8,279,040 | 2,431× |

For example, the fresh product is a nonsquare modulo 7. For every guess $s$, the discriminant $s^2-4N$ is then nonzero modulo 7. If it passes modulo 7, it automatically passes modulo 49. The same holds there for 11, 13, 17 and 19. Only 3 and 5 require their second digit. The crossed product requires the second digit at 3, 5, 7 and 19. Multiplying the required moduli together with 4 gives the periods above. The Chinese remainder theorem constructs the allowed offsets from the much smaller individual tables, one offset per compatible choice. [Local lifting and least periods](../PrimeFactors/MinimalPrimeSquarePeriod.lean) · [CRT equivalence](../PrimeFactors/FactorSumCRT.lean)

Why can no shorter repeating list give exactly the same yes-or-no answers? If a set of $c$ residues modulo $m$ is unchanged by adding $t$, the sum of all its elements is unchanged too. That sum increases by $ct$, so $m$ divides $ct$. For a square product at an odd prime $p$ coprime to $N$, the number of accepted residues modulo $p^2$ is congruent to 2 modulo $p$. Thus a period must be divisible by $p^2$. For a nonsquare product the same argument forces divisibility by $p$, and lifting shows this suffices. The full pattern has to preserve each separate condition. This proves minimality for an ordinary repeating list of pass/fail answers. Other representations, such as the separate small tables, can use far less space. [Translation argument and CRT periods](../PrimeFactors/MinimalPrimeSquarePeriod.lean)

## How many lookups does an ordinary scan save?

The seven first-digit tables take 75 bits in all if each residue gets one bit. Using $p^2$ for all seven takes 1,023 bits. Keeping just the digits needed for the same answers takes **101 bits** on the fresh product and **485 bits** on the crossed product, before alignment and bookkeeping. A scan can check the tables in order from smallest passing fraction to largest and stop at the first rejection. The earlier scan already used the best complete-period order for the seven ordinary prime tables. [Lookup-count method and first-digit baseline](what-ordering-saves-on-the-full-width-interval.md)

| Published product | Ordered prime lookups | Ordered prime-square lookups | Further reduction |
| --- | ---: | ---: | ---: |
| Fresh | $1.14302\times10^{306}$ | $8.51322\times10^{305}$ | About 25.52% |
| Crossed | $5.18265\times10^{306}$ | $3.67076\times10^{306}$ | About 29.17% |

Counts in the table are rounded and cover the entire public interval. One lookup is charged for each candidate that reaches each of the seven stages. Square tables can eliminate candidates earlier and also reduce the number that need a final integer square test. The cost model excludes setup, indexing a larger table and the machine cost of a remainder. It gives no wall-clock factoring time. [Finite-interval lookup certificates](../PrimeFactors/PublicPrimeSquareLookupCosts.lean)
