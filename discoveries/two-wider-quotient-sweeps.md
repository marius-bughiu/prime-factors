# Wider intervals for a complete divisor search

Given only an odd product $N=pq$ with $p\le q\le2p$, a complete sweep can recover the smaller factor by searching intervals in $[\lceil\sqrt{N/2}\rceil,\lfloor\sqrt N\rfloor]$. Two changes to the project's quotient sweep nearly double its guaranteed interval width. They apply to every such product. On eight previously published products of 25-bit primes, a narrower setting recovered every pair in 2.70 seconds of CPU time for the group, down from 3.78 seconds. At 2,048 bits the full search remains infeasible. [Previous sweep](quotient-search.md) · [Measured results](../research/secant-quotient-comparison.json)

## Which integer points have to be searched?

Write a possible factor as $x=a+mt$, where the wheel $m$ is even and coprime to $N$, and $a$ runs through its invertible residues. The old sweep used the tangent to the reciprocal function modulo $m^2$. Instead, take the line through its values at the consecutive class positions $a$ and $a+m$. The product of consecutive integers is even, so

$$
(x-a)(x-a-m)=m^2t(t-1)\equiv0\pmod{2m^2}.
$$

The identity $x(2a+m-x)=a(a+m)-(x-a)(x-a-m)$ now determines the ordinate. Compute the single inverse $J=(a(a+m))^{-1}\bmod 2m^2$. Every true pair $xy=N$ in that class satisfies

$$y\equiv NJ(2a+m-x)\pmod{2m^2}.$$

The horizontal step stays $m$ and the vertical step doubles. A triangle with vertices in this lattice has an integer signed determinant divisible by $2m^3$. There are still $\varphi(m)$ classes and one inverse per class. With $m=210$ the resulting vertical modulus is $88{,}200$, which also retains the universal relation $y\equiv Nx\pmod{24}$ for these units. [Lean lift and determinant](../PrimeFactors/SecantQuotientCells.lean)

There is a limit to further lifting by the same device. Suppose three consecutive positions $a,a+m,a+2m$ all admit ordinates with $xy\equiv N\pmod T$. If one affine formula fits all three modulo $T$, their second difference vanishes. Multiplying this difference by $a(a+m)(a+2m)$ gives $2Nm^2\equiv0\pmod T$. For $N$ coprime to $T$ this forces $T\mid2m^2$. The three-position condition holds at every modulus supported on the primes of the even wheel. Other moduli can omit positions because they are nonunits. [Lean second-difference bound](../PrimeFactors/SecantQuotientCells.lean)

## Which points can the interval contain?

On $A\le x\le B$, set $H=B-A$. Measure a point's distance below the chord of the hyperbola using the integer $E=N(A+B-x)-AB y$. For a true pair,

$$
E=y(x-A)(B-x),\qquad 0\le4A E\le N H^2.
$$

The upper bound follows from $y\le N/A$ and $4(x-A)(B-x)\le H^2$. This gives two **parallel** enclosing lines. Each cell still takes two Euclidean floor sums to count. The coordinates $(x,4AE)$ form a rectangle of width $H$ and height $NH^2$. The absolute determinant of three points in a rectangle is at most its width times its height. Transforming back divides the bound by $4A^2B$. Because the original determinant is a multiple of $2m^3$, every occupied cell is collinear whenever

$$ NH^3 < 8m^3 A^2 B. $$

The old sufficient condition had $1$ in place of $8$. For a uniform sweep, let $L$ be the first position in the balanced band and use the conservative right-hand side $8(mL)^3$. This doubles the allowed real span. With integer rounding the new width is either twice the old integer width or one less when the band length does not cap the widths. A collinear cell requires at most one quadratic to recover its factor pairs. [Lean containment and collinearity](../PrimeFactors/SecantQuotientCells.lean) · [Search implementation](../experiments/secant_quotient_cells.py)

Wider cells can contain more points and require additional moment calculations to recover their line. The default therefore uses coefficient $4$. The old triangle's area divided by its lattice index is $NH^3/(2m^3A^2B)$. For the parallel strip the corresponding ratio is $NH^3/(8m^3A^2B)$. Increasing the width by $4^{1/3}$ matches the leading geometric ratio and reduces the number of cells by about $37\%$ at fixed wheel and large $N$. This area comparison determines the setting independently of the prime factors.

## What did the complete searches cost?

All searches used wheel 210, visited the whole band, and checked the same factors. Each time is the median of five local CPU-time measurements cycling the order of the three methods. The proof generator separately certified the recovered factors of all sixteen holdout products in Lean. Each Euclidean count starts with two floor sums per cell. Moment computations and quadratic solves are charged separately. [Comparison program](../experiments/secant_quotient_comparison.py) · [All counters and timings](../research/secant-quotient-comparison.json)

| Input group | Sweep | Cells | Moment states | Quadratics | CPU seconds |
|---|---|---:|---:|---:|---:|
| $1{,}900{,}014{,}700{,}027$ | Previous | 1,200 | 30,664 | 34 | 0.066 |
| | Equal area | 768 | 18,993 | 17 | 0.041 |
| | Maximum proved width | 624 | 30,876 | 61 | 0.070 |
| Eight pairs of 16-bit primes | Previous | 1,200 | 17,478 | 25 | 0.040 |
| | Equal area | 768 | 12,512 | 16 | 0.029 |
| | Maximum proved width | 768 | 20,477 | 59 | 0.050 |
| Eight pairs of 25-bit primes | Previous | 66,816 | 1,635,991 | 1,493 | 3.779 |
| | Equal area | 42,192 | 1,120,790 | 939 | 2.695 |
| | Maximum proved width | 33,504 | 1,773,289 | 3,022 | 4.280 |

For the first row, both new schedules returned $1{,}000{,}003\times1{,}900{,}009$. The normal benchmark also checks this product and prime factors in Lean. The previous complete odd trial sweep on this small number took about 0.008 seconds. The measured gain is against the earlier quotient sweep. [Benchmark fixtures](../benchmarks/secant-quotient-cells.json) · [Earlier trial comparison](quotient-search.md)

## What changes on a 2,048-bit product?

On the independently generated, certified fresh product, each method searched exactly the same interval. Its first integer was the midpoint of the public balanced band, rounded down. Its length was four old wheel-210 widths, a 351-bit integer. The three searches returned no factor. The separately certified smaller prime lies outside that interval. [Fresh product and generation](certified-fresh-control.md) · [Exact interval, search results and full-band counts](../research/secant-quotient-fresh-window.json)

| Sweep | Tested cells | Counting Euclidean steps | Moment states | Quadratics | CPU seconds, one run | Planned full-band cells |
|---|---:|---:|---:|---:|---:|---:|
| Previous | 192 | 78,095 | 195,655 | 4 | 0.936 | $2.77\times10^{204}$ |
| Equal area | 144 | 57,637 | 132,127 | 2 | 0.656 | $1.75\times10^{204}$ |
| Maximum proved width | 144 | 38,518 | 195,925 | 8 | 0.889 | $1.39\times10^{204}$ |

The last column counts a complete schedule arithmetically. Only the common interval was searched. The factor-search exponent stays the same. The implementation reuses the project's MIT-licensed floor sums, moments and line recovery. Reproduce the small comparison with `python3 experiments/secant_quotient_comparison.py`, and the full-size bounded control with the additional option `--fresh-window`. [Quotient implementation](../experiments/quotient_search.py) · [License](../LICENSE)
