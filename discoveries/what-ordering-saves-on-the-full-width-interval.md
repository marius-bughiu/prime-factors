# What does changing the test order save at 2,048 bits?

On both published 2,048-bit products, reordering seven odd-prime tests saves **about one quarter of the small remainder lookups** in a full scan. The better order would still need more than $10^{306}$ lookups on either product. This is a proved work count for an exhaustive scan. The calculation used each public product, the published factor widths and small modular tables. It did not run that scan. [Full-interval proof](../PrimeFactors/PublicWheelLookupCosts.lean)

| Product | Lookups in increasing prime order | Lookups in increasing order of passing fraction | Saving |
| --- | ---: | ---: | ---: |
| Fresh | $1.51466\times10^{306}$ | $1.14302\times10^{306}$ | 24.5362% to 24.5363% |
| Crossed | $6.87203\times10^{306}$ | $5.18265\times10^{306}$ | 24.5833% to 24.5834% |

The absolute counts in the table are rounded. Each scan checks the public modulo-four condition first, then applies the same seven odd primes through 19 to the surviving sums. Only their order changes. Consequently the same sums reach the final integer square test. Earlier work bounded those final counts at more than $2^{1008}$ on the fresh product and $2^{1011}$ on the crossed product. [Earlier survivor bounds and scope](how-far-public-remainders-narrow-the-sum.md#what-do-inexpensive-remainders-save-at-2048-bits)

## Counting the work without performing the scan

The seven tests repeat every 4,849,845 candidate positions when stepping through sums four at a time. The Chinese remainder theorem gives the number surviving each group of preceding tests in a full period. Add these counts to get the number of lookups. Any incomplete final period contributes between zero and one full period’s work. [CRT proof](../PrimeFactors/FactorSumCRT.lean) · [Work and endpoint bounds](../PrimeFactors/PublicWheelLookupCosts.lean)

| Product | New order | Lookups per full period before | Lookups per full period after |
| --- | --- | ---: | ---: |
| Fresh | 7, 11, 13, 17, 19, 5, 3 | 11,488,825 | 8,669,895 |
| Crossed | 11, 13, 17, 19, 7, 5, 3 | 11,977,429 | 9,032,970 |

Consider any product coprime to these seven primes. At an odd prime $p$, a square product residue allows $(p+1)/2$ sum residues. A nonsquare allows $(p-1)/2$. Each prime therefore gives two choices for the fraction of candidate sums that pass. Over a complete joint period, checking the least permissive primes first minimizes the number of equal-cost lookups. [Local counts and independence](../PrimeFactors/SevenPrimeFilterSavings.lean) · [Proof that the order minimizes lookup count](../PrimeFactors/IndependentFilterOrdering.lean)

Among the 128 combinations, **126 save work** when reordered. The two ties occur when the product is a nonsquare at every test prime through 17, regardless of its behavior at 19. The smallest positive saving is 180 lookups per period, roughly 0.00237%. The largest is 2,992,699, roughly 24.986%. Each of the 128 patterns occurs at exactly 12,960 invertible product residues modulo the period. That frequency describes uniform sampling of residues. The experiment did not sample a population of large semiprimes. [Exhaustive classification and exact fractions](../PrimeFactors/SevenPrimeFilterSavings.lean)

## What changes in a short window?

An exact integer square test has a cost too. Suppose it costs $c$ lookup units to check one survivor, and each small filter costs one unit. Over a complete joint period, a filter passing a fraction $a$ of the candidates is worth including when $(1-a)c>1$. Sorting those worth including by increasing passing fraction minimizes the combined work among every subset and order. A filter exactly at the threshold can be omitted without loss. This is a cost model for independent tests with known fractions. [Optional-filter theorem](../PrimeFactors/OptionalFilterCost.lean)

On the actual 39-bit window the measured stage sizes give another calculation. Keeping ten primes in the public density order takes 12,726 lookups and leaves two square tests. Keeping twelve takes 12,730 and leaves one. For any nonnegative integer price $c$, among the fourteen possible prefixes an optimal choice uses zero primes at prices 0–1, ten at 2–4, and twelve at 5 or higher. At price 4 both ten and twelve tie. These prices are hypothetical. The counts do not measure a processor’s cycle costs. [Finite optimal-prefix proof](../PrimeFactors/PublicSumFinalTestCost.lean) · [Original 39-bit lookup comparison](how-far-public-remainders-narrow-the-sum.md#which-remainder-should-we-check-first)

Moving a window can reverse the preferred order. For the published small-product residue 665 modulo 1,716, check 3 first on four consecutive eligible sums. Putting 13 before 11 then saves a lookup at 122 starts and two at three more. It costs one extra lookup at 80 starts and ties at 224. Overall it saves 48 lookups across all 429 starts. The sign of a saving for one specified start remains sensitive to its position. [Worked product residues](when-pair-counts-determine-a-common-sum.md#all-429-starting-positions) · [Phase-by-phase count](../PrimeFactors/FilterSwapPhaseMoment.lean)

There is also a way to calculate the variation using the local tables. For any shift $h$, count how often a single prime’s table passes at both a position and the position $h$ steps later. CRT combines these single-prime counts across a full period. In a window of length four there are four pairs at separation zero, three at separation one, two at separation two, and one at separation three. Counting both directions for nonzero shifts gives a sum of squared lookup savings of $4\cdot72+2(3\cdot0+2\cdot0-37)=214$. This identity gives the second moment averaged over starts. Direct use of the lag formula for a length-$w$ window still sums $w$ lags. [Window identity and four local correlations](../PrimeFactors/FilterSwapPhaseMoment.lean)
