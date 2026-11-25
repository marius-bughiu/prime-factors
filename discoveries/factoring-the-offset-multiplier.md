# Factoring the offset multiplier

Suppose the input is the product of two unknown primes with `17 ≤ p < q ≤ 2p`. Every successful offset test has a multiplier that splits into two nearby integers. Generating these integers directly preserves all successful tests. On all 1,234 products of two distinct 7-, 8- or 9-bit primes of the same width, it reduced the square-root tests from 161,418 to 47,197. The two 2048-bit controls still have complete-search upper bounds above $2^{1019}$ coordinate visits. [Original offset schedule](complete-offset-search.md) · [One or two winning tests](one-or-two-winning-tests.md)

## What can be inferred from the product?

Write $T=\lfloor\sqrt N\rfloor$, $h=N-T^2$, $J=\lfloor\sqrt{4h/3}\rfloor$ and $K_j=\lfloor Tj/h\rfloor+1$. For a successful coprime position $(j,k)$ in the range $1\le j\le J$, $1\le k\le K_j$, there are positive, coprime $s,v$ with

$$
k=sv,\qquad j+2Tsv=ps^2+qv^2,\qquad pj=(ps-Tv)^2+hv^2.
$$

The orientation puts the smaller prime on $s^2$. The balance and size assumptions imply $4h<p^2$, hence $j<p$ and $|ps-Tv|<p$. Since $p\le T$, integrality gives $s\ge v$. For any public lower bound $0<L\le p$, the strict inequality $L(s-1)<Tv$ gives the inclusive loop

$$
1\le v\le\lfloor\sqrt{K_j}\rfloor,\qquad
v\le s\le\min\left(\lfloor K_j/v\rfloor,\lceil Tv/L\rceil\right).
$$

When both primes have $b$ bits, take $U=2^b-1$ and $L=\max(2^{b-1},\lceil N/U\rceil)$. The promise about factor width is part of the input specification. Under the weaker promise $q\le2p$, $L=\lceil\sqrt{N/2}\rceil$ also works. The search forms $k=sv$, tests the two coprimality conditions, and checks whether $j^2+4k(Tj-hk)$ is a nonnegative square. A square supplies the original gcd test. The term $+1$ in $K_j$ matters. For $117449=257\cdot457$, the only successful position has $j=17$, $s=4$, $v=3$ and $k=12=K_{17}$. [Proof of the endpoint example](../PrimeFactors/CompleteOffsetExample.lean) · [Coordinate proof](../PrimeFactors/OffsetWinnerWindow.lean)

The minimizing vector gives a further relation to the hidden ratio $T/p$. For every integer pair $(a,b)$ with $0<b<v$, it satisfies $|ps-Tv|<|pa-Tb|$. Compare $pQ(s,v)=(ps-Tv)^2+hv^2$ with $pQ(a,b)$ and use $hb^2<hv^2$. Using this best-approximation property directly would require access to $T/p$. The loop uses only $T$ and $L$. [Theorem `minimum_best`](../PrimeFactors/OffsetWinnerWindow.lean)

## Bounding all loop iterations

Put $D=T-L$ and $r_j=\lfloor\sqrt{K_j}\rfloor$. Each $(j,v)$ inner loop has at most $\lfloor Dv/L\rfloor+2$ entries. This follows from $s-v\le\lceil Dv/L\rceil$, with both endpoints included. The product cutoff in the loop can reduce the count further. Counting repeated values of $k$ every time, write

$$
V_j=\sum_{v=1}^{r_j}\left(\lfloor Dv/L\rfloor+2\right).
$$

Then $2L V_j\le D(K_j+r_j)+4Lr_j$, since $r_j^2\le K_j$. Put $S=\sum_{j=1}^J K_j$ and $R=\lfloor\sqrt{K_J}\rfloor$. Summing and rounding down gives a public upper bound on the number of coordinate visits,

$$
\left\lfloor\frac{D(S+JR)+4LJR}{2L}\right\rfloor.
$$

The existing Euclidean floor-sum algorithm computes $S$ exactly without walking the rows. There are at most $JR$ iterations of the outer $(j,v)$ loop. Each inner iteration also incurs a product and up to two gcd tests. Several coordinate pairs can generate the same $(j,k)$, so the implementation counts every visit and deduplicates only the reported successful positions. These distinctions matter when comparing a coordinate-visit bound, square tests, and elapsed time. [Lean count bounds](../PrimeFactors/OffsetWinnerWindow.lean) · [Reference search](../experiments/offset_winner_window.py)

## Complete small searches

Both scanners exhausted their entire schedule. The census constructed the prime products, then supplied only each product and the same-width promise to the search. The number of distinct successful positions matched the raw scan on every product. Every reported gcd, prime, cofactor and product was independently checked in Lean.

| Prime bits | Products | Distinct successful positions | Original positions | Coordinate visits | Original square tests | Coordinate square tests |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 7 | 78 | 81 | 5,316 | 3,129 | 2,915 | 1,380 |
| 8 | 253 | 266 | 33,928 | 17,512 | 19,367 | 6,922 |
| 9 | 903 | 965 | 239,311 | 108,425 | 139,136 | 38,895 |
| **Total** | **1,234** | **1,312** | **278,555** | **129,066** | **161,418** | **47,197** |

Four rounds over the same products, alternating the order of the complete Python scans, took median times of 0.078 s for the raw schedule and 0.050 s for the coordinate schedule on the development machine. These timings include each implementation's counters and floor-sum setup. They exclude generation of the products and verification of the output. The cost of a gcd, division and square root depends on operand size, so the small-input timing gives no estimate for a complete 2048-bit search.

## Bounded 2048-bit controls

| Product | Upper bound on coordinate visits, log₂ | Upper bound as fraction of original positions | Coordinate visits run | Square tests run | Proper splits |
| --- | ---: | ---: | ---: | ---: | ---: |
| Fresh | 1019.3474 | 6.772% | 64 | 26 | 0 |
| Crossed | 1020.4083 | 16.563% | 64 | 22 | 0 |

Both bounded runs returned the entire input as unresolved. The bounds apply to this way of enumerating the original rectangle. They are larger than the number of candidate tuples in the repository's projective reconstruction method. [Capped fixtures and exact counts](../benchmarks/offset-winner-window.json) · [Reconstructing winning positions](reconstructing-winning-positions.md)

Reproduce the counts, timings, and kernel replay from the repository root.

```sh
python3 -m experiments.offset_winner_window --census --census-certificate /tmp/window-census.lean
lake env lean -DwarningAsError=true /tmp/window-census.lean
python3 -m experiments.offset_winner_window --timing
python3 -m experiments.offset_winner_window --controls --max-visits 64
```
