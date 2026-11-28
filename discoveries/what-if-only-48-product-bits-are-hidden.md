# What if only 48 product bits are hidden?

Suppose you can read **2,000 of the 2,048 bits** of a product of two distinct 1,024-bit primes. The first 1,024 and the last 976 bits are visible. Can you guess the exact sum of its factors? Across all eligible products, even the best rule that gives one guess succeeds **less than once in 6.7 million**. The count gives equal weight to each eligible product. It uses an unconditional lower bound on the number of prime pairs, checked in this repository. [Counting theorem](../PrimeFactors/MissingMiddleSumPopulation.lean) · [Prime-pair denominator](../PrimeFactors/ChebyshevPrimeSample.lean)

Even if someone who knows the complete product sends **16 extra bits** of their choosing, the success rate stays below **1%**. For a given pair of outer words, the message can select from at most 65,536 different guesses. This includes the replies to 16 adaptive yes-or-no queries if the questioner chooses each question from the visible words and previous replies. A method using the complete product has access to all 48 middle bits. The theorem gives a cost for discarding information and puts no time limit on calculations with the retained information. [Lists and additional messages](../PrimeFactors/MissingMiddleSumPopulation.lean)

## Why very few products share a guess

Keep the exact sum fixed and write each pair in increasing order. Increasing the smaller factor from $p$ to $a=p+d$ makes the larger factor drop from $q$ to $b=q-d$. The increase in the product is $d(b-p)$, at least $d^2$ because $b\ge a$. A fixed leading word puts the products in a bin of width $2^{1024}$. Thus two smaller factors in that bin, with the same sum, must differ by less than $2^{512}$. Knowing the smaller factor's remainder modulo $2^{512}$ now distinguishes its position. [Spacing proof](../PrimeFactors/MissingMiddleSumPopulation.lean)

The trailing bits supply those remainders. If $2^v$ is the largest power of two dividing the gap between one pair of factors, then at fixed sum and fixed 976-bit product suffix, every other smaller factor agrees with one of the original factors modulo $2^{976-v}$. When $v\le464$, there are at most two positions in the bin. The exceptional pairs have a gap divisible by $2^{465}$. There are at most $2^{1024}\cdot2^{559}$ such pairs, even if we count composite factors too. [Two possible remainders](../PrimeFactors/HighLowSumPopulation.lean) · [Counting the exceptions](../PrimeFactors/MissingMiddleSumPopulation.lean)

There are $2^{1023}$ possible leading words and $2^{975}$ odd trailing words. A list with at most $J$ guesses per observation therefore covers at most $2^{1024}\cdot2^{559}+2\cdot2^{1023}\cdot2^{975}J$ eligible pairs. Dividing by the proved population gives the stated rates. The earlier result about 482 visible bits uses a prime-count estimate under Dirichlet GRH and describes every eligible setting of those bits. The result here bounds the overall success rate on a different, larger observation. [Earlier prefix and suffix theorem](which-true-sums-can-share-the-same-leading-and-trailing-bits.md)

## Four bits that matter on one small product

Start with **40,270,613**. We selected this example because four single-bit changes each produce another pair of distinct 13-bit primes. Every change flips the same output bit, bit 2 of the factor sum. Bit positions start at zero.

| Changed product bit | Product | Prime factors | Sum | Sum modulo 8 |
| --- | ---: | --- | ---: | ---: |
| Original | 40,270,613 | 5,897 × 6,829 | 12,726 | 6 |
| 2 | 40,270,609 | 6,053 × 6,653 | 12,706 | 2 |
| 3 | 40,270,621 | 4,943 × 8,147 | 13,090 | 2 |
| 4 | 40,270,597 | 6,151 × 6,547 | 12,698 | 2 |
| 22 | 36,076,309 | 5,303 × 6,803 | 12,106 | 2 |

A rule that skips position 22 on the original product receives the same answers on 36,076,309, including when it chooses its next query from previous answers. It must give the same answer on both, so it fails on one. Each of the other three positions has its own witness. Lean checks the decision-tree argument, all five factorizations, and the bit changes. [Certificates and query theorem](../PrimeFactors/ToySumBitQueries.lean)
