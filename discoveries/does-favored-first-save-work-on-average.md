# Does trying the favored sums first save work on average?

**Yes. Across all products of two distinct 1,024-bit primes with a 2,048-bit product, the priority order saves more than 1/95 of the exact square tests in total.** That is more than 1.05%, counting every product where it costs extra and every product where it makes no difference. Each product has equal weight. Within the subset whose product is 1 or 4 modulo five, the saving exceeds **2.5%**. Both comparisons use a published unconditional prime-count bound at modulus five as an explicit input to Lean. [All products and unique successful tests](../PrimeFactors/MeanAllSumOrderWork.lean) · [Products congruent to one or four](../PrimeFactors/MeanSumOrderWork.lean) · [Bennett, Martin, O’Bryant and Rechnitzer, Theorem 1.3](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5)

This gives a comparison between two elementary exhaustive searches. Each uses the product and the known bit width of its factors, applies the same remainder filters, and counts one exact square test per surviving sum it tries. The result compares the sums of those counts across the population. Individual inputs can take longer, and the accounting excludes the work of generating the candidates. Even on more than 24.9% of all balanced 2,048-bit products where the priority order saves at least 70%, it still requires at least $2^{894}$ square tests. [How the search works and how much work remains](when-two-remainders-save-square-tests.md)

## Where the gains and losses come from

Split the surviving sum guesses into two groups using only the public product $N$. A guess $s$ is favored when $s^2-4N$ is divisible by five. Every interval of 100 consecutive integers has two favored and five other passing sums for this product family. If the true sum is favored, the search saves all ordinary tests before it. Otherwise it pays for every favored sum above the true sum. These two identities give exact counts even in an incomplete final block. When the product is 2 or 3 modulo five, no sum has the favored remainder. Both orders then visit exactly the same candidates and stop at the same square. [Remaining product residues](../PrimeFactors/AllResidueSumCost.lean) · [Proof of both identities](../PrimeFactors/GlobalSumOrderCost.lean)

For example, two twelve-bit prime pairs each needed 24 ascending square tests. The favored-first search needed **seven** on $8{,}402{,}929=2{,}053\times4{,}093$, and **25** on $8{,}488{,}399=2{,}081\times4{,}079$. Every row below covers all pairs of the given width with a full-width product congruent to 1 or 4 modulo five. Both searches tested actual squares and recovered the factors. [Reproduce the census](../experiments/whole_width_sum_order.py)

| Bits per prime | Eligible products | Ascending tests | Favored-first tests | Tests saved on favored hits | Extra tests on other hits |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 8 | 72 | 81 | 80 | 7 | 6 |
| 9 | 263 | 350 | 339 | 43 | 32 |
| 10 | 852 | 1,568 | 1,477 | 334 | 243 |
| 11 | 2,745 | 7,420 | 7,057 | 1,960 | 1,597 |
| 12 | 9,744 | 46,345 | 43,118 | 14,330 | 11,103 |
| 13 | 32,314 | 278,325 | 262,247 | 91,963 | 75,885 |
| 14 | 114,255 | 1,919,694 | 1,783,089 | 661,879 | 525,274 |

At fourteen bits, the favored-first order won on 47,966 inputs, tied on 12,993 and lost on 53,296. The wins were large enough to save 136,605 tests overall. Building the lists in this small demonstration also took 19,716,960 residue lookups and 5,529,755 priority classifications. The first pooled saving in widths two through fourteen occurred at seven bits, with one test saved across 21 products. [Census and regression checks](../tests/test_whole_width_sum_order.py)

## Why the conclusion holds at 2,048 bits

Write $B=2^{1024}$, $x=p/B$ and $y=q/B$, with $p<q$. The distance from the lower search endpoint to the true sum is approximately $B(\sqrt y-\sqrt x)^2$. The room remaining after the true sum is at most $B(1-x)(1-y)$. The proof bounds the effects of integer rounding and of the last partial block explicitly. These two lengths measure the costs of a win and a loss. [From integer test counts to lengths](../PrimeFactors/NormalizedSumWork.lean)

Divide each coordinate into intervals of width $1/256$. There are 4,922 complete rectangles inside the factor and product bounds and 5,124 rectangles that can contain an eligible pair. Credit for saved work uses only complete rectangles. The upper bound on extra work also includes every possible boundary rectangle. Lean checks bounds on both lengths within each rectangle, with exact integer arithmetic for the finite table. [Geometric bounds and table](../PrimeFactors/MeanSumOrderGeometry.lean)

The unknown factors' remainders modulo five determine which cost applies. There are four ordered pairs of nonzero remainders with equal entries, and four with opposite entries. The published prime-count estimate bounds the number of primes in each class in every coordinate interval. Each eligible prime pair belongs to exactly one rectangle and one group. Combining the lower bound on credits with the upper bounds on losses and baseline work gives the strict 2.5% net saving. [Counting actual prime pairs](../PrimeFactors/SumGridPopulation.lean) · [Summing the costs](../PrimeFactors/SumOrderAggregation.lean)

For the full-population theorem, eight more ordered pairs of factor remainders produce the two other product classes. All their square tests enter the baseline total and they contribute zero saving. Including their cost gives the lower guarantee of **1/95** over all the products. [Prime counts in the remaining groups](../PrimeFactors/OtherSumGridPopulation.lean) · [Full-population work inequality](../PrimeFactors/MeanAllSumOrderWork.lean)

A separate continuous model, in which $x,y$ are uniformly distributed by area and the local residue pairs have equal weight, predicts a saving of about **7.04%** within the square-product classes. The 2.5% guarantee uses bounds for actual prime counts and allows less favorable behavior in every boundary rectangle. [Reproduce the model and its rational bounds](../experiments/mean_sum_order_geometry.py)
