# Which sum fits the most factor pairs?

Suppose you know the upper half of a product’s bits and want to make one guess for the sum of its two factors. Which guess fits the most pairs of odd integers? **You only need to compare two sums.** Take the largest product consistent with the known bits, find its square root, and double both the floor and the ceiling. One of those sums has the highest possible count. If the factors must both be prime, a different sum can win.

For example, take the 14-bit upper word 8,197, with two 14-bit factors. The three rows below count actual pairs whose product has those upper bits. Each pair is counted once, with its smaller factor first.

| Proposed sum | Pairs of distinct odd integers | Pairs of distinct primes |
| ---: | ---: | ---: |
| 23,178 | 36 | 0 |
| 23,180 | 29 | 1 |
| 23,182 | 20 | 3 |

The first two sums come from the square-root rule. The first is an optimal guess over odd integer pairs. The third fits more prime pairs than the first two combined. Its three prime pairs are $11{,}369\times11{,}813$, $11{,}393\times11{,}789$ and $11{,}399\times11{,}783$. [Ranking theorem and checked example](../PrimeFactors/HighWordSumRanking.lean)

## What the theorem counts

Set $B=2^b$. Each factor lies between $B/2$ and $B-1$, and the product has $2b$ bits. An upper word $h=\lfloor N/B\rfloor$ places the possible products in the interval from $n=Bh$ through $T=Bh+B-1$. For **every** $b\ge14$ and eligible $h$, Lean proves that at least one of $2\lfloor\sqrt T\rfloor$ and $2\lceil\sqrt T\rceil$ fits as many distinct odd factor pairs as any other proposed sum. This includes 2,048-bit products, with $b=1{,}024$. A separate finite calculation also found the property on all 8,191 eligible words at widths $b=1$ through $13$. [Finite-pair theorem](../PrimeFactors/HighWordSumRanking.lean) · [Bounds on the square roots](../PrimeFactors/HighWordSumRankingBounds.lean)

To evaluate one guess $2u$, write the factors as $u-v$ and $u+v$. The half-gap $v$ must be positive, have the opposite parity to $u$, and lie between $L$ and $U$.

$$L=\max\!\left(1,\left\lceil\sqrt{\max(0,u^2-T)}\right\rceil\right),\qquad
U=\min\!\left(\left\lfloor\sqrt{u^2-n}\right\rfloor,u-B/2,B-1-u\right).$$

A row is empty when $u^2<n$ or $u$ lies outside the factor range. Otherwise start at the first $v\ge L$ of the required parity. If $v>U$ the count is zero. If $v\le U$ it is $1+\lfloor(U-v)/2\rfloor$. At full size, selecting a most-populated integer row costs one integer square root to locate the two midpoints and at most two more per midpoint to count them. These operations use roughly 2,048-bit integers. They rank sums across *all* products with the given upper word. For a particular product the chosen sum is still a guess. [Exact counting rule](../PrimeFactors/HighWordSumRanking.lean)

## Why only two sums need comparing

Every earlier midpoint has square below $n$, so its row is empty. At later midpoints, the possible interval for the half-gap shrinks. In the unclipped range, moving past the ceiling of $\sqrt T$ costs at least two units of interval width. Half-gaps of the required parity are spaced two units apart. When a factor-size limit clips the interval, each possible pair in a later row maps to a different pair in the ceiling row by keeping its smaller factor. This proves the bound even with rounding at both ends. [Interval-width estimate](../PrimeFactors/HighWordSumRankingBounds.lean) · [Counting the parity and factor-width restrictions](../PrimeFactors/HighWordSumRanking.lean)

A separate exhaustive count at 14 bits included 228,713 eligible prime pairs across 7,965 occupied upper words. Picking the single most common *prime* sum for each word covered 19,901 pairs. Picking the better of the two square-root guesses, using the prime counts to choose between them, covered 16,300. Both choices in this comparison had access to the completed census. [Prime-pair census](../research/high-word-sum-ranking.json)

Choosing the more populated *integer* row using the upper word alone recovered 14,926 of the 228,713 products. Taking the first ordinary Fermat midpoint from the whole product recovered 17,324. The integer-row rule found 83 that the first Fermat test missed, while the first Fermat test found 2,481 that the integer-row rule missed. On the two 2,048-bit controls the rule used three and four setup roots respectively, followed by one square test each. Both products remained unsplit. [Product-only experiment](../experiments/high_word_sum_ranking.py) · [Benchmark inputs and budgets](../benchmarks/high-word-sum-ranking.json)
