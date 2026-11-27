# Choosing a factor sum from the high word and a remainder

Suppose two distinct odd integers each have $b$ bits, and their product $N$ has $2b$ bits. Given the upper $b$ bits of $N$ and its remainder modulo $m$, which sum fits the most pairs of integers? **One of $P+1$ consecutive even sums attains the global maximum**, where $P=\operatorname{lcm}(2,m)$. The proof applies when $b\ge14$, $m\ge1$ and $2^b\ge4096P^3$. It counts each pair once, with the smaller integer first. [Lean ranking theorem](../PrimeFactors/HighWordSuffixRanking.lean)

For instance, two 66-bit products share the upper word 4,294,967,296 and have remainder 41 modulo 120. Both readings select the sum 12,148,002,030, or midpoint 6,074,001,015. That sum recovers **6,073,583,363 × 6,074,418,667** for the first product, 36,893,488,155,787,837,121. For the second, 36,893,488,155,852,544,481, the correct midpoint is 6,074,001,009. It gives **6,073,682,449 × 6,074,319,569**. This earlier midpoint was the first permitted by the remainder in ordinary Fermat search for both products. The two examples were deliberately selected from those two rows. They show that identical readings can favor one sum while a different sum factors a particular input. [Benchmark cases and checked factors](../benchmarks/high-word-suffix-ranking.json)

## Which sums to count

Put $B=2^b$, $h=\lfloor N/B\rfloor$, $n=Bh$, $T=n+B-1$ and $a=\lfloor\sqrt T\rfloor$. The known high word puts the product in $[n,T]$. Compare midpoints $a,a+1,\ldots,a+P$ and propose twice the midpoint with the largest count. For midpoint $u$, write the factors as $u-v$ and $u+v$. The legal half-gaps $v$ are the positive integers of parity opposite to $u$ for which

$$
B/2\le u-v<u+v<B,\qquad n\le u^2-v^2\le T,\qquad
v^2\equiv u^2-N\pmod m.
$$

The first two conditions give an interval with integer square-root endpoints. The last condition and parity give a set of residue classes modulo $P$. Each class can be counted with two integer divisions using the endpoints. The implementation tabulates $P$ residue entries, considers $P+1$ rows, and skips a row when its class list is empty. Counting an occupied row takes up to two integer square roots and one count per permitted residue. For each 66-bit example, the ranking used 120 table entries, 121 row positions, 25 setup square roots in total and 64 residue-class counts. Testing the chosen midpoint against the actual product used one more integer-square test. [Implementation](../experiments/high_word_suffix_ranking.py)

For a full-width product with $b\ge14$, charging the ranking setup to a single input gives a stronger cost comparison. Ordinary Fermat can start at $\lceil\sqrt N\rceil$ and test every midpoint permitted by the same remainder up to a successful ranked guess. Each of those positions already cost the ranking at least one setup square root. Including each method’s initial root and the ranked guess’s final square test, the direct scan recovers the same factors with strictly fewer square roots. Sharing a computed ranking across multiple inputs changes the setup charge. [Cost comparison and factor readout](../PrimeFactors/HighWordSuffixCost.lean)

## Why later rows cannot win

The floor midpoint $a$ handles the lower side of the upper endpoint. Every smaller row is empty. Of the next $P$ rows, one represents each midpoint residue modulo $P$. Compare any higher occupied row with that first representative of its class. If a factor-width endpoint limits the earlier row, subtracting the difference between midpoints from each later gap gives distinct gaps in the earlier row. The difference is a multiple of $P$, so parity and the known product remainder survive.

In the other case the full interval between the square roots fits in the earlier row. Write $w=B-1$ and $g(d)=\sqrt{d+w}-\sqrt d$ for its real width, with $d=u^2-T$. At the earlier representative $d\le2BP$. By the next row of the same class, $d$ has increased by at least $BP$. Rationalizing the square roots shows that the later interval has lost at least $P$ units of width under the stated size assumptions. Translating all later gaps back by one fixed multiple of $P$ then places them inside the earlier interval. This gives an injection for every union of allowed residue classes simultaneously. [Interval bounds and translation](../PrimeFactors/HighWordSuffixTransfer.lean) · [Earlier result using only the high word](which-sum-fits-the-most-factor-pairs.md)

## What happens for prime pairs

The census used every pair of distinct primes of the indicated width with a full-width product. The ranking used the earliest midpoint in case of a tie. The comparison took the first ordinary Fermat midpoint compatible with the same remainder. The entries below count products recovered in one final square test. Ranking and ordinary Fermat have different setup costs. All eight small panels fall below the size bound for the global maximum theorem. [Complete census, including gains and losses per product](../research/high-word-suffix-ranking.json)

| Factor bits | Prime pairs | Ranked, mod 24 | Fermat, mod 24 | Ranked, mod 120 | Fermat, mod 120 |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 8 | 148 | 138 | 132 | 147 | 144 |
| 10 | 1,718 | 1,015 | 995 | 1,524 | 1,235 |
| 12 | 19,546 | 6,432 | 6,558 | 11,248 | 8,767 |
| 14 | 228,713 | 41,248 | 42,241 | 64,531 | 57,568 |

At 14 bits and modulus 120, ranking gained 9,493 factorizations and lost 2,530 relative to **one** remainder-compatible Fermat guess. Simply taking the earliest occupied row in the same word-based block recovered 62,507. For 214 products, every row in the block was empty. At modulus 24, the first remainder-compatible Fermat guess recovered 993 more products than ranking. [Search and comparator definitions](../experiments/high_word_suffix_ranking.py)

**With the same total square-root budget per input**, the remainder-compatible Fermat scan recovered 192,183 of the 228,713 products at modulus 120, compared with 64,531 for ranking. At modulus 24 the counts were 111,623 and 41,248, respectively. The scan used one root to find its starting midpoint and spent the rest on successive midpoints allowed by the remainder. In all eight census panels, ranking recovered zero products that this equally budgeted scan missed. These counts compare square-root budgets and do not measure elapsed time. [Per-panel root budgets and recovery counts](../research/high-word-suffix-ranking.json)

## The two 2,048-bit controls

At modulus 120, neither ranking nor the equal-budget scan found a factor on the independently generated product or on the product made by crossing the known primes. Each ranking considered 121 row positions. Each Fermat scan started at the ceiling square root of the actual product and tested consecutive remainder-compatible midpoints. [Full-size benchmark inputs, work and unresolved cofactors](../benchmarks/high-word-suffix-ranking.json)

| Input | Ranked setup roots + final square test | Fermat starting root + remainder-compatible square tests | Outcome on both searches |
| --- | ---: | ---: | --- |
| Independently generated | 25 + 1 | 1 + 25 | Whole product unresolved |
| Crossed primes | 49 + 1 | 1 + 49 | Whole product unresolved |

The first remainder-compatible Fermat guess also missed both products. In the earlier comparison using only the high word, ranking took three setup roots on the independently generated input and four on the crossed input, followed by one square test each. Both missed, as did ordinary Fermat's first unfiltered midpoint on each input. [High-word-only benchmark and ordinary Fermat control](../benchmarks/high-word-sum-ranking.json)

At 1,024 bits per factor the size bound holds for modulus 120. It guarantees that 121 rows suffice to maximize the **integer-pair count** for a known word and remainder. Each input has a single correct prime-factor sum. The experiment gives no full-size success rate or time bound for finding that sum. [Scope of the ranking theorem](../PrimeFactors/HighWordSuffixRanking.lean)
