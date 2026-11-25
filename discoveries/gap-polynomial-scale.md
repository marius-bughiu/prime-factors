# Monic polynomials in the balance gap

For balanced prime factors of an odd 2,048-bit product, a degree-eight equation now needs a factor remainder modulo $2^{568}$, one bit below the full-factorial Newton bound of $2^{569}$. Each new odd remainder class joins two of the previous classes. At degree four the bound stays at $2^{615}$. The gain comes from the small difference between comparable factors and is less than one bit before rounding the radix. The degree-eight guarantee still leaves $2^{567}$ odd remainders before reciprocal and sign symmetries. [Newton congruences and comparison](difference-lanes.md) · [Lean proofs](../PrimeFactors/GapPolynomialScale.lean)

## What happened when we ran the search

All three methods recovered the prime pairs on the same eight 31–32-bit products. Each used signed groups and the full Newton divisibility test. The only change was the choice of coordinates for the equation. Lean checked all eight factorizations. The timing column sums the three-run median on each product. [Replay](../experiments/gap_newton_lanes.py) · [Counts and timings](../research/gap-newton-lanes.json)

| Coordinates | Lattice reductions | Root-isolation nodes | Seconds |
| --- | ---: | ---: | ---: |
| Powers of the factors | 504 | 3,180 | 0.208 |
| Powers of their difference | 385 | 5,184 | 0.185 |
| Dickson polynomials in the difference | 363 | 6,744 | 0.186 |

On the fresh 2,048-bit comparison product, the complete counts were about $2.804\times10^{183}$, $2.127\times10^{183}$ and $1.985\times10^{183}$ groups, respectively. The last is a 29.2% reduction compared with ordinary Newton coordinates on this input. We tested two groups under each rule. All three runs took about 5.7–5.9 seconds and left the entire product unresolved. Each rule chooses its own radix, so the three prefixes can represent different possible factors. [Fresh input and independent construction certificate](certified-fresh-control.md) · [Two-group fixture](../benchmarks/quartic-factor-lanes.json)

## The product gives an even gap interval

Let $N=xy$ for positive odd factors with $x\le2y$ and $y\le2x$. The search knows only $N$ and the balance assumption. With $D=x-y$, the identity
$$xy-2D^2=(2x-y)(2y-x)\ge0$$
gives $D^2\le N/2$. Since $D$ is even, the integer $s=\lfloor\sqrt{N/8}\rfloor$ gives the interval $|D|\le2s$. Write $B=\lfloor\sqrt{2N}\rfloor$, so $|x|\le B$. Negating both factors preserves all these bounds and allows the signed remainder search to continue using the same equation. If $s=0$, every balanced odd factor pair is a square pair and an integer square-root test resolves the case.

## Integral coordinates on the same factor pairs

For $s>0$ take $C=s^2$ and the Dickson polynomials $P_0=2$, $P_1=D$ and $P_{j+2}=D P_{j+1}-C P_j$. Use $E_0=1$ and $E_j=P_j$ for $j\ge1$. For a chosen power $t\ge1$, use the $2t+1$ integer traces
$$1,\ E_1(D),\ xE_0(D),\ E_2(D),\ xE_1(D),\ldots, E_t(D),\ xE_{t-1}(D).$$

Every $E_j$ is monic of degree $j$. To compare to the old coordinates in $x$ and $y$, expand $(x-y)^j$ and reduce each mixed term by $xy=N$. The new terms at degree $j$ are $x^j+(-1)^j y^j$. The only term of degree $j$ in $x E_{j-1}(x-y)$ after reduction is $x^j$, also for $j=1$. Thus the change at degree $j$ has rows $(1,(-1)^j)$ and $(1,0)$, with determinant $\pm1$. Descending through these pairs gives an integer inverse for the whole matrix. Multiplication by $x^t$ still gives an ordinary nonzero polynomial of degree at most $2t$. Guessing $x\bmod R$, testing the Newton grid and finding the integer roots use the same public congruences as before. The congruence lattice index is unchanged by this integral change of basis. [Full-factorial lattice index](difference-lanes.md)

## Why the uniform coordinate bound is sharp on the gap interval

Write $U_0=0$, $U_1=1$, $U_{j+2}=D U_{j+1}-C U_j$. Direct induction gives
$$P_j^2+(4C-D^2)U_j^2=4C^j.$$
On $|D|\le2s$ this proves $|E_j(D)|\le A_j=2s^j$ for every $j\ge1$. Set $A_0=1$ for the constant coordinate. The two weights at degree $j$ are therefore $A_j$ and $B A_{j-1}$. All weights are positive integers.

These gap weights attain the minimax bound among real monic polynomials of each degree on the entire continuous interval. Substituting $D=2s\cos\theta$ into the recurrence gives $P_j(D)=2s^j\cos(j\theta)$. At the $j+1$ points $2s\cos(k\pi/j)$ the values alternate between the two extrema. A monic polynomial with strictly smaller maximum absolute value would differ from $P_j$ by a polynomial of degree at most $j-1$ with a zero between each successive pair of points, which is impossible. The interval's logarithmic capacity is consequently $\lim_{j\to\infty}(2s^j)^{1/j}=s$. The actual integer factor gaps form a subset of this interval. The calculation leaves open tighter bounds on that subset, on the coupled coordinates $xE_{j-1}$, and on combinations of several coordinates. [Classical Chebyshev minimax theorem](https://dlmf.nist.gov/18.38.i)

## The resulting radix

The product of the column weights is exactly
$$W=\prod_{j=1}^t A_j B A_{j-1}=2^{2t-1}B^t s^{t^2}.$$
For $d=2t$, $m=2t+1$, write $J_d=\prod_{j=0}^d j!$. The scaled lattice determinant is its original congruence index times $W$. Under the same LLL estimate as the Newton construction, the strict sufficient inequality is
$$R^{2tm}J_d^2>m^m\,2^{tm} W^2.$$
As usual this full $J_d$ assumes $\gcd(N,Rd!)=1$. For a balanced 2,048-bit semiprime, both prime factors exceed the degrees in the table. In general one can use the parts of the factorials coprime to $N$. [Reduced-factorial case](difference-lanes.md)

For $N<2^{2048}$, $B^2\le2^{2049}$ and $s^2\le2^{2045}$. The exponent bounding $W^2$ is consequently $K_D=4t-2+2049t+2045t^2$. Ordinary powers in $x,y$ give $K_0=2049t(t+1)$. Plain powers $D^j,xD^{j-1}$ give $K_1=2049t+2047t^2$. Each entry below is the least $e$ satisfying the same strict comparison with $R=2^e$ and the indicated uniform $K$. These are guaranteed scales, with no assumption about which remainder contains the factor pair.

| Degree $2t$ | Powers in $x,y$ | Powers in $D$ | Dickson polynomials in $D$ |
| ---: | ---: | ---: | ---: |
| 2 | 684 | 684 | 684 |
| 4 | 615 | 615 | 615 |
| 6 | 586 | 585 | 585 |
| 8 | 569 | 569 | 568 |
| 16 | 541 | 541 | 541 |
| 64 | 517 | 517 | 516 |
| 1,024 | 506 | 505 | 505 |
| 4,096 | 504 | 503 | 503 |

To verify any table column, use the integer comparison $2^{2etm}J_d^2>m^m2^{tm+K}$ at $e$ and $e-1$. The large-degree interval certificate in the Newton note applies verbatim with the corresponding $K$. Lean checks all winning exponents in the Dickson column through degree 16, the failure at one smaller exponent, the polynomial identity and monicity, the integral inverse for the leading pair, the product of the column weights and the strict one-bit comparison. The polynomial change of basis follows by the degree reduction above. [Formal statements](../PrimeFactors/GapPolynomialScale.lean) · [Integer interval certificate](difference-lanes.md)

Relative to the ordinary full-factorial bound, the improvement to the continuous base-two logarithm of the radix is
$$\frac{K_0-K_D}{2tm}=\frac{4t^2-4t+2}{2t(2t+1)}<1.$$
It approaches one bit as $t$ grows. Even after rounding to a power of two the guaranteed reduction from this replacement is at most one bit. Smooth integer radices and orbit counts can round differently, and no full-search time follows from these bounds.
