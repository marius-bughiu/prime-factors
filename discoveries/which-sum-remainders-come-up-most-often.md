# Which sum remainders come up most often?

Take a product that leaves remainder 1 on division by 25. Its two factors can have a sum ending in any of **seven** remainders modulo 25. In the complete population of nine-bit prime pairs with that product remainder, **21 of 44** sums fall in just two classes, 2 and 23. All 44 products are different. This suggests trying those two remainders first when looking for the exact sum. [All 44 pairs and their verified frequencies](../PrimeFactors/PrimePairSumFrequency.lean)

## Where the bias comes from

There are 20 ways to choose a first factor remainder coprime to 25. Once it is chosen, its inverse is the only possible second remainder for a product of 1. Giving each of those 20 ordered pairs equal weight gives the middle row below. The final row uses every eligible pair of distinct nine-bit primes once, with the smaller prime first.

| Sum remainder | 0 | 2 | 5 | 10 | 15 | 20 | 23 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Ordered remainder pairs | 2 | 5 | 2 | 2 | 2 | 2 | 5 |
| Actual nine-bit prime pairs | 6 | 8 | 6 | 2 | 3 | 6 | 13 |

For any odd prime $p$, fix a product remainder coprime to $p$. When the product is a square modulo $p$, exactly two sum remainders modulo $p^2$ have $s^2-4N=0$ modulo $p^2$. Each has **$p$ ordered factor pairs**. Every other possible sum has exactly two. The first two sums therefore account for $2/(p-1)$ of the pairs in the uniform remainder model. No other choice of two remainders captures a larger fraction. For $p=5$ this gives one half. Drawing one sum guess according to the model, independently of the actual nine-bit product, gets the remainder right on 151 of 880 equally weighted draws (17.16%). Choosing uniformly from the seven allowed sums gives one in seven (14.29%). [General formula and optimal two residues](../PrimeFactors/PrimeSquareSumWeights.lean) · [Finite comparison](../PrimeFactors/PrimePairSumFrequency.lean)

## How much can ordering the remainders save?

Suppose you guess the true **sum remainder** by crossing off a different class on each guess. Give all ordered factor residue pairs with the fixed square unit product equal weight. Visiting the two most frequent classes first minimizes the mean number of guesses. The largest relative saving over a random order, for any single odd prime square, is **$10/51$, about 19.61%**, at modulus 49. The mean falls from $17/2$ to $41/6$ guesses. Modulo 25 the saving is 18.75%. These count distinct remainder guesses. If many integer sums share a remainder, locating the right integer incurs additional work. [Optimal order and sharp bound](../PrimeFactors/PrimeSquareExpectedRank.lean)

## What happens when we search for the actual primes?

Both searches take the product and factor width as input. They keep the same list of sums after checks modulo 4 and 25. The baseline visits sums in increasing order. The alternative visits the sums with $s^2-4N$ divisible by 5 first, in increasing order within each group. Each visit takes one exact integer square root to test whether $s^2-4N$ is square. When it is, the two factors are $(s-\sqrt{s^2-4N})/2$ and $(s+\sqrt{s^2-4N})/2$. [Candidate list and correctness proof](../PrimeFactors/ToyResidueOrderCost.lean)

| Bits per prime | Products with square unit remainder modulo 25 | Ascending checks | Priority checks | Earlier / tied / later |
| --- | ---: | ---: | ---: | ---: |
| 9 | 441 | 603 | 579 | 70 / 319 / 52 |
| 10 | 1,375 | 2,440 | 2,347 | 326 / 736 / 313 |
| 12 | 16,129 | 77,334 | 72,162 | 5,694 / 4,074 / 6,361 |

The 12-bit group saved **5,172 exact square checks** (6.69%). More products finished later than earlier. The larger improvements on the earlier finishes account for the aggregate saving. Preparing these priority lists also classified 199,891 candidate positions. The totals measure square checks, and the classification cost matters for runtime. Among **all** 32,385 distinct twelve-bit prime pairs, both searches recovered every pair and the counts were 182,400 and 177,228 checks. [Bounded replay with cost counters](../experiments/toy_residue_order_cost.py)

For a concrete win, $101{,}951=269\times379$ has the true sum at check 2 in ascending order and at check 1 with priority. For $128{,}251=277\times463$, priority moves the answer from check 2 to check 4. A whole subgroup also reverses the result. On the 136 ten-bit prime pairs with product remainder **1** modulo 25, prioritizing those sums required **259 checks**, up from **242**. Lean checks this subgroup and the two nine-bit comparisons. The bounded replay checks both returned factors on all 36,063 pairs across the three widths, with no assumption on product width. Run it with `python3 -m experiments.toy_residue_order_cost`. [Lean certificates](../PrimeFactors/ToyResidueOrderCost.lean) · [Reproducible search](../experiments/toy_residue_order_cost.py)

## What carries over to 1,024-bit primes?

For a prime interval, let $C_x$ be the number of primes in class $x$. Each ordered pair of different factor classes contributes $C_x C_y$ actual ordered prime pairs. A repeated class contributes $C_x(C_x-1)$ so the same prime is never used twice. Summing over the desired classes and dividing by two counts distinct unordered pairs. This identity holds for every modulus and directly connects the local weights with true prime-pair frequencies. [Exact finite formula](../PrimeFactors/ResiduePairWeights.lean)

Now give equal weight to all pairs of distinct primes between $3\cdot2^{1022}$ and $2^{1024}$ whose product is 1 modulo 25. Both primes have 1,024 bits and every product has 2,048 bits. A published unconditional prime-count bound places the share with true sum 2 or 23 modulo 25 **between 49.9% and 50.1%**. It controls how many primes each of the 20 allowed factor classes contains. Lean checks the deduction from the two endpoint estimates. [Full-size population proof](../PrimeFactors/UnconditionalPrimePairSumFrequency.lean) · [Bennett, Martin, O’Bryant and Rechnitzer, Theorem 1.3](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5)

The stronger published prime-count estimates under Dirichlet GRH sharpen this to **one half with absolute error at most $2^{-477}$**. The estimates themselves are external inputs to this repository. The frequency describes a population of different integer products. Each remainder can still include an enormous number of exact sums for an individual product. [Full-size theorem and analytic inputs](../PrimeFactors/WidePrimePairSumFrequency.lean) · [Ernvall-Hytönen and Palojärvi, Corollary 2](https://arxiv.org/pdf/2003.01925#page=2)

## What about all eligible 2,048-bit products?

A nine-bit example shows the difference between the two populations. Of the 44 prime pairs with product 1 modulo 25, **27** have a full eighteen-bit product. Fifteen of those have sum 2 or 23 modulo 25. Restricting both primes to the upper half of the nine-bit range leaves only 11 products, eight with those sum remainders. The broader population includes $152{,}701=311\times491$, whose sum is 802. [Complete finite comparison](../PrimeFactors/PrimePairSumFrequency.lean)

We can now remove the restriction that both primes lie in the upper half of their interval. Give equal weight to **every** pair of distinct 1,024-bit primes with a 2,048-bit product congruent to 1 modulo 25. The share whose sum is 2 or 23 modulo 25 differs from one half by **at most $1/1648$**, using the published unconditional estimates. That guarantees a percentage strictly between 49.9% and 50.1%. Using the Dirichlet-GRH estimates gives an absolute error of at most $2^{-480}$. Both proofs take the respective published prime-count inequalities as inputs. [Exact population definition](../PrimeFactors/PrimeProductRegion.lean) · [Full-population bounds](../PrimeFactors/FullRangePrimeSumShare.lean)

The product-width condition matters because smaller primes need larger partners. Fix the first prime $p$ and write $B=2^{1024}$. The eligible partners lie between $\lfloor 2^{2047}/p\rfloor$ and $B$. This is always a final segment of the same prime interval. The published estimates bound the difference between prime counts in *any* two unit classes in *every* such segment. Substituting another remainder class for one factor therefore has a uniformly bounded cost in the count of prime pairs. Swapping the roles of the two primes lets us apply the same argument to the other factor. The proof then removes pairs with identical primes and counts each product once. [Counting pairs above the product threshold](../PrimeFactors/ThresholdPairCount.lean) · [Uniform estimates for every segment](../PrimeFactors/FullRangeResidueEstimates.lean) · [Unconditional source, Theorem 1.3](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5)
