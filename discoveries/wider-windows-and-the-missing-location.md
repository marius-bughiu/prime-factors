# How much ground can one equation cover?

One equation now checks about **70 trillion times as many possible odd factors** at a chosen location as our previous quartic. We tried the larger equation on two 2,048-bit products. Lean verified that each chosen interval was empty. We can also reuse several smaller equations to check neighboring intervals. On a complete 49-bit search this more than halved the number of lattice reductions, though total runtime was slightly higher. We still need a way to choose a location containing a prime. [Fresh large interval](https://marius-bughiu.github.io/prime-factors/#higher-divisor-window-fresh-2048) · [Crossed large interval](https://marius-bughiu.github.io/prime-factors/#higher-divisor-window-crossed-2048) · [Complete small search](https://marius-bughiu.github.io/prime-factors/#adaptive-quartic-cover-49)

## How the product gives one equation per location

Suppose we know only the odd product $N$ and that the sought factor has 1,024 bits. Choose an odd center $c$ publicly and write a possible divisor as $d=c+2x$, with $|x|\le W$. Let $t=(N-c)/2$. If $d$ divides $N$, it divides $x-t$. For an integer polynomial $F$, impose $N^{m-j}\mid [Y^j]F(t+Y)$ for $0\le j<m$. At a divisor every term in the expansion of $F(x)$ is then divisible by $d^m$. If the sum of $|a_i|W^i$ over the coefficients of $F$ is below $d^m$, the only possible value of $F(x)$ is zero. Its integer roots give a short list of offsets for trial division. The location and the polynomial can both be chosen without knowing the factor. [General proof and coverage](../PrimeFactors/HigherDivisorWindow.lean)

Here is what this guarantees when $N<2^{2048}$ and $d\ge 2^{1023}$. The third column is a radius in odd-number indices. A window contains $2W+1$ odd positions. The last column counts an explicit grid covering the entire 1,024-bit odd band, including any portion that the particular product or a known upper bound on the smaller prime could remove.

| Polynomial degree | Multiplicity $m$ | Radius $W$ | Locations for the complete grid |
| ---: | ---: | ---: | ---: |
| 4 | 2 | $2^{407}$ | $2^{614}$ |
| 8 | 4 | $2^{453}$ | $2^{568}$ |
| 16 | 8 | $2^{480}$ | $2^{541}$ |
| 50 | 25 | $2^{500}$ | $2^{521}$ |
| 1,043 | 521 | $2^{510}$ | $2^{511}$ |

Lean proves existence by counting distinct Taylor remainders. For construction, the basis polynomials $N^{m-i}(X-t)^i$ for $i<m$ and $X^{i-m}(X-t)^m$ for $i\ge m$ span the required lattice. Scaling coefficient $i$ by $W^i$ gives determinant $N^{m(m+1)/2}W^{k(k+1)/2}$ at degree $k$. The classical LLL first-vector estimate guarantees a short row for the tabulated parameters. The formal proof checks the numerical inequality and the existence of a polynomial at every center. The LLL first-vector theorem comes from the published analysis. These are applications of the classical unknown-divisor small-root method. [May, Theorems 6–7](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38) · [Lenstra, Lenstra and Lovász, Proposition 1.6](https://doi.org/10.1007/BF01457454)

We ran the nine-row construction at the public lower quartile on each full-size control. It took 3,061 row swaps and 5,291 size reductions on the fresh input, and 3,087 swaps and 5,473 size reductions on the crossed input. On this machine each first reduction took about 49 CPU seconds. The resulting degree-eight polynomials had no root modulo 3 and 2 respectively. Lean checked every Taylor divisibility, the coefficient bound and the full residue table. Each certificate rules out $2^{455}+1$ consecutive integers around the center, including even positions. On 2,501 the same construction at center 43 found 41 and 61. The higher-degree rows in the table are theorem bounds. We have not run their full grids. [Measured work](../benchmarks/higher-divisor-window.json) · [Factor certificate for 2,501](https://marius-bughiu.github.io/prime-factors/#higher-divisor-window-2501)

## How far growing the degree can take this bound

With $k+1$ rows, radius $2^w$, lower divisor bound $2^{1023}$ and product upper bound $2^{2048}$, the classical first-vector estimate implies the desired height when

$$(k+1)^{2(k+1)}2^{4096m(m+1)+(2w+1)k(k+1)} < 2^{4092m(k+1)}.$$

For $w=510$, **1,044 is the smallest possible number of rows** passing this particular inequality, even if we choose the best multiplicity. It works with $m=521$. For the lower bound, put $j=k-2m$ and let $E$ be the exponent on the right minus the exponent on the left. Completing the square gives $E\le k(k-1023)+(k+1)^2/1024$. When $k\le1022$ its integer value is at most zero. For $1023\le k\le1042$ it is at most $20(k+1)$, already accounted for by the dimension factor. At $k=1043$, $m=521$, $E=21924=21\cdot1044$ and $1044^2<2^{21}$. The same height estimate never guarantees $w=511$. A particular lattice or another way of bounding its shortest vector can do better. [Lean dimension proof](../PrimeFactors/DivisorWindowDimension.lean) · [Radius bound](../PrimeFactors/HigherDivisorWindow.lean)

May’s Theorem 7 handles small roots of a monic degree-$\delta$ polynomial modulo an unknown divisor of size at least $N^\beta$. Here the input polynomial is linear, $X-t$. At $\beta=\log_N(2^{1023})$ its classical radius $N^{\beta^2}$ already exceeds $2^{511}$ on these inputs. The classical algorithm can use translated subintervals and multiple auxiliary equations. It still requires choosing the overall interval. The published capacity obstruction for roots modulo the full input concerns a different hypothesis. [May, Theorem 7](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38) · [Cohn and Heninger, Theorem 1.1](https://arxiv.org/pdf/1008.1284#page=2) · [Chinburg et al., scope](https://arxiv.org/pdf/1605.08065#page=20)

## Reusing equations across consecutive locations

For a quartic row $F$, an actual divisor $d=c+2x$ always makes $F(x)/d^2$ an integer. On the next interval that integer can be positive or negative even when the old height bound has failed. We bound its possible integer values there. At each residue of $x$ modulo a small prime, every equation must permit the same offset. If the permitted offsets have empty intersection, the entire interval is free of divisors. Otherwise a row with a short list of levels gives a few ordinary polynomial equations to check. If the checks do not cover a chunk, the sweep starts a new reduction there or records it as unvisited when it reaches its budget. [Lean exclusion theorem](../PrimeFactors/QuarticLevelExclusion.lean) · [Search](../experiments/adaptive_quartic_cover.py)

| Complete search of 502,005,281,288,939 | Lattice reductions | Median CPU seconds |
| --- | ---: | ---: |
| Fixed quartic windows | 4,827 | 0.604 |
| Reuse one quartic | 2,661 | 0.697 |
| Reuse up to five quartics | 1,984 | 0.631 |

All three searches recovered $17{,}838{,}631\times28{,}141{,}469$. The last one covered all 2,814,129 odd positions, checked 195 individual polynomials for integer roots and tried one divisor. It also spent 168,320 modular row evaluations. Times are medians of three interleaved runs per method on the same machine. On the two full-size inputs, five reductions reached 15 and 19 successive old chunks. Both products remain unresolved. For each, the downloadable certificate checks one chunk outside the original height window where two rows together exclude every offset modulo 11. [Full work counts](../benchmarks/adaptive-quartic-cover.json) · [Fresh certificate](https://marius-bughiu.github.io/prime-factors/#adaptive-quartic-cover-fresh-2048) · [Crossed certificate](https://marius-bughiu.github.io/prime-factors/#adaptive-quartic-cover-crossed-2048)

## Could one formula tell us which half to search?

For $N=22{,}663$, the product of the integers in $[107,128]$ has gcd one with $N$. The product in $[129,150]$ has gcd 131. Computing the product of all 44 positions already returns the same factor by gcd. The cost is evaluating the products. [Worked example](../PrimeFactors/FactorIntervalProduct.lean) · [Previously tested factorial batches](batch-intervals.md)

There is a precise limit on one attempt to avoid that evaluation. Fix a prime $p$ and $2W\le p$. Suppose a single polynomial modulo $p$ has to output zero on the first $W$ possible consecutive offsets and one on the next $W$. Its first difference vanishes at $2W-2$ distinct points and is nonzero at the transition. It follows that the polynomial needs degree at least $2W-1$, and interpolation attains that degree. A ratio of two polynomials can implement the selector with maximum degree $W$, which is also optimal. This describes a formula that must work at every promised translation. It leaves open formulas specialized to a product and fast evaluation of a high-degree formula. [Sharp degree bounds and rational construction](../PrimeFactors/FactorIntervalProduct.lean)
