# Choosing the same sum with small square roots

For the 121 candidate sums selected by the high product word and remainder modulo 120, a fixed table can often certify which sum fits the most odd integer pairs. On each of the two 2,048-bit controls, it reduced the ranking setup to **one input-dependent square root**, down from 25 on one input and 49 on the other. Testing the selected sum took one further square root. Both products remained unfactored. [Implementation](../experiments/fractional_word_ranking.py) · [Benchmark inputs](../benchmarks/fractional-word-ranking.json)

## How the table preserves the choice

Each midpoint has an interval of possible half-gaps. The upper product bits set its endpoints, and the remainder determines which gap residues to count. For each endpoint the table supplies lower and upper bounds on its square root. Counting admissible gaps in the inner interval gives a guaranteed minimum. Counting them in the outer interval gives a maximum. A row wins as soon as its minimum exceeds every earlier row’s maximum and reaches every later row’s maximum. The strict comparison on earlier rows preserves the original tie rule. If the bounds overlap, the implementation computes exact endpoints for the rows that could still win. [Lean proof](../PrimeFactors/FractionalWordRanking.lean) · [Original exact scoring](choosing-a-sum-from-a-word-and-a-remainder.md)

For precision $k$, entry $a$ stores the floor and ceiling of $2^k\sqrt a$. To bracket $\lfloor\sqrt x\rfloor$, choose $h$ a power of two so that $a=\lfloor x/h^2\rfloor$ fits in $k$ bits. The inequalities $ah^2\le x<(a+1)h^2$ provide both endpoints using table entries $a$ and $a+1$ and bit shifts. When $h=1$ the lower endpoint is already exact. The 12-bit table stores 4,097 rows, computed once from 4,097 square roots of integers at most 37 bits long. [Table construction, lookup and refinement](../experiments/fractional_word_ranking.py)

## What the savings buy

The census includes every eligible product of two distinct 14-bit primes. Each row below has 228,713 products. The comparison gives ordinary Fermat search the same remainder and the same per-product allowance of input-dependent square roots as ranking spent, including setup and the final test. Table generation, lookups and counts of allowed residues are separate costs. [All 16 panels at 8 through 14 bits](../research/fractional-word-ranking.json)

| Modulus | Table precision | Products factored by ranking | Products factored by Fermat at the same root budget |
| ---: | ---: | ---: | ---: |
| 24 | 8 bits | 41,248 | 42,531 |
| 24 | 12 bits | 41,248 | 41,280 |
| 120 | 8 bits | 64,531 | 73,285 |
| 120 | 12 bits | 64,531 | 57,862 |

With 12-bit precision and modulus 120, ranking gained 9,069 products and lost 2,400. It used 228,713 initial roots, 9,140 refinement roots and 223,340 final square tests. It also needed 10,310,042 table reads and 20,453,120 residue-class counts, each with two integer divisions. Across the 135,512 distinct high-word and remainder readings in this panel, caching the completed rankings would cut the table reads to 6,122,976. A local Python comparison on each full-size control found the table implementation slower than both the original exact ranking and the single-guess Fermat scan with the table already initialized. The advantage measured here is in the number of input-dependent roots. [Operation counts for individual inputs and cached readings](../research/fractional-word-ranking.json)

Two deliberately selected 66-bit products share the same upper word and remainder. After the table has been built, ranking and Fermat each use one initial root and one final check. Ranking recovers the first pair, $6{,}073{,}583{,}363\times6{,}074{,}418{,}667$. Fermat recovers the second, $6{,}073{,}682{,}449\times6{,}074{,}319{,}569$. Across the full 2,048-bit target population, the proportion for which **any** of the 121 guesses could work is below $2^{-491}$. [Constructed examples](../benchmarks/fractional-word-ranking.json) · [Full-size coverage proof](how-often-the-121-sums-can-work.md)
