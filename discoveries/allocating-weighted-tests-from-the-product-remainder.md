# Allocating fifteen tests from the product remainder

We fixed this allocation before counting its factor discoveries. Start with sixteen ordinary tests. Spend one root to start each of the two weighted searches and allocate the remaining fifteen square tests from $r=N\bmod24$. The budget is 34 roots. The comparison always uses seven tests for $(3,2)$ and eight for $(7,5)$.

| $r$ | Average spacing for $(3,2)$ | Average spacing for $(7,5)$ | Tests for $(3,2)$ | Tests for $(7,5)$ |
|---|---:|---:|---:|---:|
| 1, 13 | 3 | 24 | 3 | 12 |
| 5, 7, 17, 19 | 3 | 12 | 5 | 10 |
| 11, 23 | 3 | 6 | 8 | 7 |

For weights $(a,b)$, the projected interval length per unit of $N^{1/4}$ is $2(b/a^3)^{1/4}\sqrt{sH}$, where $s$ is the mean spacing between admissible labels and $H$ is the number tested. This is a width estimate with the trace endpoint replaced by its average. For each residue, maximize the sum of the two estimates over all 16 integer allocations from zero to fifteen. An exact tie goes to fewer $(3,2)$ labels. Integer fourth-root bounds certify a unique winner for each residue. Evaluation uses the same product range as the fixed search and counts actual successful gcd splits. [Geometry-only table generator](../experiments/residue_batch_allocation.py) · [Original search and product range](using-two-factor-ranges-after-sixteen-tests.md)

## Did the new allocation actually find more factors?

Yes, on all four complete prime populations below. At 26 bits per prime, about **1.17% more products split in the second stage**. Including the common prefix, the fraction of products split rose from about 1.515% to 1.524%. Some products previously found were lost. [Counts by remainder and bit size](../research/residue-batch-allocation.json)

| Bits per prime | Extra splits with 7+8 | Extra splits with the public rule | Gained | Lost | Net gain |
|---:|---:|---:|---:|---:|---:|
| 16 | 142,452 | 143,777 | 9,410 | 8,085 | 1,325 |
| 20 | 5,818,060 | 5,884,012 | 500,440 | 434,488 | 65,952 |
| 24 | 258,705,622 | 261,683,493 | 22,237,736 | 19,259,865 | 2,977,871 |
| 26 | 1,754,407,933 | 1,774,849,195 | 150,907,629 | 130,466,367 | 20,441,262 |

Every remainder had a positive net gain at each bit size. At 16 bits we ran the square and gcd tests on every product and checked each discovery against its sieved prime factors. An independent count using intervals of possible prime partners gave the same results for each remainder, including the numbers gained and lost. At the larger sizes we used the prime-partner count. Its fixed-schedule totals agree with the previous census. The result for general 2,048-bit products remains unknown. [Reproduce the counts](../experiments/residue_batch_comparison.py) · [Why prime-partner counting works](how-the-short-search-scales.md)

For $2,416,459,631=39,581\times61,051$, the product remainder was 23. The extra eighth $(3,2)$ test found the factors. For $2,417,096,389=39,607\times61,027$, the remainder was 13. The fixed allocation split it on the seventh $(3,2)$ test, while the public rule moved to the other range after three tests and missed. Both examples were selected after counting to illustrate the two possible changes. All three 2,048-bit fixtures ran the full budgets without a split. [Decimal inputs and expected outcomes](../benchmarks/residue-batch-allocation.json)

Run the two counts from the repository root.

```sh
python3 -m experiments.residue_batch_comparison --direct 16
python3 -m experiments.residue_batch_comparison 16 20 24 26
```
