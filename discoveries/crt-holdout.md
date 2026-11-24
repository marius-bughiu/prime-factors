# Testing the two searches on 64 new products

We compared the square-quotient search and ordinary continued fractions on 64 new 79-bit products. The short square search recovered **none**. The larger square search recovered **13**, and the continued-fraction search recovered **15**. Together the last two methods recovered 16 different products. All three used only the public product for discovery. [Individual results and budgets](../research/crt-holdout.json) · [How square quotients produce factors](crt-square-norms.md)

| Settings fixed before drawing the sample | Products split | Rows examined across all 64 | Combined square relations tested |
| --- | ---: | ---: | ---: |
| A. First 12 eligible primes, triples in order, $|Q|\le\lfloor16\sqrt N\rfloor$, at most 1,001 roots | 0 | 64,064 | 239 |
| B. Same triples, $|Q|\le\lfloor4\sqrt N\rfloor$, at most 10,000 roots | 13 | 445,473 | 8,681 |
| C. Ordinary continued fraction of $\sqrt N$, at most 5,138 steps | 15 | 328,832 | 564 |

The earlier 79-bit success at root 1,001 determined the budget for A. It did not repeat on these 64 inputs. B made 215,581 individual positive-square tests. One such test revealed a factor, and combining rows gave its other 12 splits. B used a median of 7,054 rows per product. C took all 5,138 steps on each product. The rows have different costs to generate and test. These budgets compare the specified searches and do not establish a general speed ranking.

| B and C on the same product | Count |
| --- | ---: |
| Both recovered the factors | 12 |
| Only B recovered them | 1 |
| Only C recovered them | 3 |
| Neither recovered them | 48 |

For the single B-only success, $540061474802074463378617=709471782571\cdot761216285227$. B collected 7,063 rows across its 220 moduli. After excluding 6,540 rows with private nonsquare factors, it found a splitting relation on its 201st basis test. This is an example where changing the source of the square congruences made a difference. The observed overlap limits how much these two particular runs helped each other on this sample.

## Sampling and verification

The fixed seed is the ASCII string `crt-screen-holdout-v1`. For each attempted pair, draw the two primes in SHAKE256 domains tagged `p` and `q`. Hash the seed, one null byte, the one-byte domain, the zero-based pair-attempt number, and the zero-based draw counter. Both counters are eight-byte unsigned big-endian integers. Take five output bytes as a big-endian integer. Set its top and bottom bits and reject composites by exact trial division through its integer square root. This maps the hash bytes uniformly to odd 40-bit candidates. The fixed hash stream makes the sample reproducible. Keep the first 64 distinct products having two distinct primes and bit length 79. Attempt 156 supplied the last product. We applied no outcome-based filtering. [Generator and search entry points](../experiments/crt_holdout.py)

The search entry point receives only $N$. The two generated primes check returned factors and certify the sample after the search. The Lean replay validates an exact factorization of every sampled product, including the products on which discovery exhausted its budget. An unresolved method records the entire product as its remaining cofactor. Reproduce the searches, generate the 64 certificates under `build/crt-holdout/`, and check them with the pinned Lean toolchain by running the following command.

```sh
python3 experiments/crt_holdout.py --verify
```
