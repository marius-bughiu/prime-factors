# Can the product remainder choose both weighted sums?

We fixed the following rule before counting any factor discoveries. For an eligible product $N$, run sixteen ordinary square tests. Take $r=N\bmod24$ and choose two new pairs of coefficients from the table. Each entry $(a,b,H)$ means to check the first $H$ admissible values of $ap+bq$. The two new starts cost two square roots. Together with the ordinary start and the 31 square tests, each schedule costs 34 roots. The comparison uses the previously published residue-dependent allocation of fifteen tests between $(3,2)$ and $(7,5)$. [Original allocation](allocating-weighted-tests-from-the-product-remainder.md)

| Remainders | First $(a,b,H)$ | Second $(a,b,H)$ |
|---|---|---|
| 1, 13 | $(7,5,9)$ | $(13,11,6)$ |
| 5, 17 | $(7,5,8)$ | $(9,7,7)$ |
| 7, 19 | $(7,5,7)$ | $(11,7,8)$ |
| 11, 23 | $(3,2,7)$ | $(11,7,8)$ |

The sole eligibility assumption used to choose slopes is the central product range $9U^2/16\le N\le5U^2/8$ for $U=2^{\text{prime bits}}$. We allow all reduced slopes $1<a/b<8/5$. Keeping a strict upper endpoint leaves the center $\sqrt{bN/a}$ inside the feasible range at its upper product boundary. For a fixed positive number $H$ of labels, the leading interval width is proportional to $(b/a^3)^{1/4}\sqrt{sH}$, where $s=24/\#\{v\bmod24:\gcd(v,24)=\gcd(a+br,24)\}$. We keep the largest coefficient for each distinct multiplier $ab$, choose the two largest remaining coefficients, and maximize their summed widths over $H=1,\ldots,14$ with $15-H$ labels on the other slope. Ties favor smaller $(a,b)$ in lexicographic order and then fewer labels on the lexicographically first slope. Positive allocations to both slopes make the two largest coefficients optimal within this leading-width model.

The finite search covers all reduced slopes in the specified range. For $a\ge64$, the coefficient to the fourth power satisfies $bs^2/a^3<24^2/64^2$. Both distinct incumbent multipliers 6 and 35 have coefficients strictly larger than this bound for every allowed remainder. Replacing any large-$a$ choice with one of them can therefore increase the objective. Rational comparisons rank the slopes, and integer fourth-root bounds certify each allocation. The model does not predict the presence of a factor at an individual location. [Geometry-only table and exact comparisons](../experiments/geometry_weight_menu.py)

## What happened when the factors had 16, 20 and 24 bits?

Each row includes every pair of distinct primes of the indicated width whose product falls in the specified range. “Gained” means only the new schedule found that pair and “lost” means only the previous schedule found it. A product split by the common ordinary prefix contributes to both totals.

| Bits per prime | Products | Previous splits | New splits | Gained | Lost | Net increase |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | 592,048 | 289,580 | 301,570 | 64,181 | 52,191 | 11,990 |
| 20 | 96,713,943 | 11,823,013 | 12,406,107 | 3,028,432 | 2,445,338 | 583,094 |
| 24 | 17,115,589,103 | 521,389,924 | 547,179,839 | 134,305,714 | 108,515,799 | 25,789,915 |

At 16 bits the change raises the success rate from 48.91% to 50.94%. Two remainders, 11 and 23, lost 696 and 619 splits respectively. All eight remainders improved at both larger widths, while overall success under the fixed budget fell to 12.83% and then 3.20%. The previous and new schedules both miss most products at these larger widths. [All counts by remainder](../research/geometry-weight-menu.json)

The 16-bit direct replay calculates square roots and gcds from the product, then checks the discovered divisors against the independently generated prime pair. A second count fixes a prime and groups its possible partners by residue and exact integer intervals. It allows every allocation of the multiplier between the two factors, including a split recovered through a different orientation from the one used to select labels. It merges each schedule's intervals before counting. These methods agree on every 16-bit subtotal. The 20- and 24-bit rows use the interval method. The new schedule had overlapping primary weighted intervals on 148,068 of the 16-bit products, and a bit-width boundary clipped at least one interval on 49,409. The direct replay counted each actual factorization once. Reproduce the results with `python3 -m experiments.geometry_weight_menu --direct 16` and `python3 -m experiments.geometry_weight_menu --census 16 20 24`. [Exact census method](../experiments/weighted_partner_counts.py)

The new schedule splits $2,415,956,311=38,393\times62,927$ in the bounded benchmark. On $2,417,258,621=39,719\times60,859$, the previous schedule succeeds and the new schedule exhausts its budget. Lean checks both factorizations, with the second recorded for the previous schedule. [Bounded comparison fixtures](../benchmarks/geometry-weight-menu.json)

## What carries over to 2048 bits?

Write $u=N^{1/4}$ and $h$ for the excess of the first omitted trace above $2\sqrt{abN}$. The condition $ap+bN/p<2\sqrt{abN}+h$ cuts out one open interval. Its exact width is

$$u\sqrt{4\sqrt{b/a^3}\,h+\left(\frac{h}{au}\right)^2}.$$

The two schedules use one weight pair in common. Its two heights have the same rounding error, because they start at the same ceiling. Keeping that dependence gives a tighter bound than independently rounding the two heights. For all eight product remainders and every $u\ge10^6$, the two new primary bands together gain at least $0.014u$ in real width. In the specified equal-width product bin they are feasible, separate from each other and from the common prefix. The gain survives endpoint rounding to integer locations. Lean also checks that an actual factor in one of these bands puts its weighted sum among the paid labels. For a multiplier coprime to the product, its square gives a factor through one gcd. [Lean width, band and integer results](../PrimeFactors/GeometryWeightMenu.lean)

At 2048 bits we replayed both searches on three existing products. Two fall inside the bin. Their new weighted bands include respectively 10.31% and 10.24% more integer positions than the previous bands, after clipping and removing the ordinary prefix. Neither schedule found a factor on either product. The third control lies outside the bin and both searches also missed it. These bands grow on the scale of $N^{1/4}$ while the feasible smaller-factor interval in this bin grows on the scale of $\sqrt N$. A wider band still needs to contain the unknown prime for the primary construction to find it. The finite census and width theorem give no general 2048-bit factorization guarantee. Reproduce the control results with `python3 -m experiments.geometry_weight_menu --controls`. [Full-size inputs](../benchmarks/interior-prime-family.json) · [Exact site counts and outcomes](../research/geometry-weight-menu.json)
