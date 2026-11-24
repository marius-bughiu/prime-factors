# Can digits of the product predict which row to search?

Each odd prime has **exactly one** normalized representation among the three quadratic forms in our smaller-prime formula. This makes it possible to measure how often a proposed rule picks the right second coordinate, even if we let it test every first coordinate for free.

For the first two forms keep the original parity restrictions. In the third form $p=2a^2-t^2$, also require $t<a$. The guaranteed representation has $t^2<p$, which implies this extra restriction. All four coordinates in a comparison of two normalized representations have squares strictly below $p$. The form itself is determined by $p$ modulo 8. For two representations $(t,a)$ and $(u,b)$ of the same prime, the ratios $t/a$ and $u/b$ are square roots of the same nonzero residue modulo $p$. Hence $p$ divides one of $tb-ua$ and $tb+ua$. Each cross product is strictly below $p$. Their sum is even, so it cannot be the only possible positive multiple of $p$ below $2p$. Their difference must therefore be zero. Proportional positive coordinates giving the same nonzero quadratic value agree. [Lean existence and uniqueness theorem](../PrimeFactors/CanonicalNorm.lean)

For balanced primes $p<q\le2p$, every retained value from the band $[L,\lfloor\sqrt N\rfloor]$ divisible by $p$ must equal $p$, since $\sqrt N<2p$. The canonical product therefore contains the smaller prime exactly once. For $51{,}937=167\cdot311$ the original band contains both $2\cdot12^2-11^2=167$ and $2\cdot14^2-15^2=167$. The strict order retains the first. It removes one of 30 candidate pairs while preserving the factorization. The candidate values still include composites. [Band product](norm-band-product.md) · [Checked example](https://marius-bughiu.github.io/prime-factors/#band-unique-167)

## A limit on choosing rows from high and low bits

Choose two distinct primes uniformly from $[X,2X)$ with $X=2^{1023}$, conditioned on a 2,048-bit product. A row consists of a form and a fixed second coordinate $a$. Suppose a rule can read the leading $h$ variable bits of the product and the trailing $k$ variable bits. We supply the leading 1 and trailing odd bit for free. The rule may pick at most $K$ rows for each observed pattern and try every odd $t\le2^{512}$ on each row. Row locations may be chosen anywhere in the full coordinate range. Randomized rules are covered by first fixing their randomness. The result also applies if the next choice depends on preceding hits or misses alone: up to the first hit the sequence follows its all-miss path. Further arithmetic on the original product during selection is outside this model.

The high bits partition $[2X^2,4X^2)$ into $C=2^h$ intervals. The low bits specify one of $J=2^k$ odd residue classes modulo $M=2^{k+1}$. Each observed pattern gives at most $K\,2^{511}$ candidate prime values in the exact representation search, since the first coordinate is odd. Fix a candidate prime $p$ and a high interval of width $W$. Its partner $q$ must lie in one residue class modulo $M$, because $p$ is odd. Distinct partners in that class give products at least $pM$ apart. There are at most $1+W/(pM)$ possibilities, counting even the composite partners. This bound holds for any set of primes chosen for each observed pattern. [Lean partner-count bound](../PrimeFactors/NormRowAdvice.lean)

Sum the bound over intervals and odd suffixes. Their interval widths sum to $2X^2$ before repeating them for the $J$ suffixes. Using $p\ge X$ gives $CJ+2XJ/M=2^{h+k}+X$. Counting either ordering of a hit, and dividing by the established lower bound on the number of ordered eligible prime pairs, gives
$$\Pr(\text{find the prime row})\le
\frac{2K\,2^{511}(2^{h+k}+X)}{(0.22X/\log X)^2}.$$
The estimate uses integer counts and $\log X<710$. It applies to fixed numbers of actual product bits, not to arbitrary functions of the product compressed into the same number of bits. [Prime-count denominator](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Exact rational calculation](../experiments/norm_row_advice.py)

| Product information used to select rows | Rows permitted | Upper bound on success |
|---|---:|---:|
| Any split of 1,023 variable bits between the two ends | $2^{450}$ | $<2^{-36}$ |
| Any split of 1,023 such bits | $2^{40}$ | $<2^{-446}$ |
| Any split of 1,469 such bits | $2^{40}$ | $<1/2$ |

In particular the first bound still holds when the rule guesses second coordinates near the largest useful ones. The simpler size exclusion for two simultaneously small coordinates gives no such conclusion for these scattered rows.

## The best possible small lookup table

We exhaustively counted all 19,546 unordered pairs of distinct 12-bit primes having a 24-bit product. For each product we used the hidden smaller prime **only to label the unique correct row**. For each observed bit pattern a hypothetical lookup table can pick the $K$ most frequent labels. That rule attains the maximum possible number of hits in this population because the labels are disjoint. Building the table uses the known answers. The results measure an information limit.

| Variable high bits | Variable low bits | Hits with one row | Hits with four rows |
|---:|---:|---:|---:|
| 0 | 0 | 778 | 2,964 |
| 8 | 0 | 1,602 | 5,029 |
| 4 | 4 | 1,537 | 4,916 |
| 0 | 8 | 1,242 | 4,083 |
| 8 | 4 | 4,485 | 12,874 |
| 4 | 8 | 4,520 | 12,888 |

All rows use the same 19,546 products. The table is exhausted by enumeration at this width; the 2,048-bit statements above come from the separate finite bound. [All counts](../research/norm-row-advice-12.json) · [Enumeration and optimality checks](../tests/test_norm_row_advice.py)
