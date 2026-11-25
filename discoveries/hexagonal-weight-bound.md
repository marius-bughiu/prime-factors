# A smaller guaranteed radix for every slope

The two factors lie on a hyperbola. Near the largest possible gap, their midpoint also has to be near its largest possible value. This rules out two corners of the old search rectangle. Accounting for both corners lowers the sufficient radix by about **7.35%** before rounding on large inputs. The guarantee holds for every slope, and the same four candidate directions still suffice to find working weights. Lean proves the result by counting a finite set of integer points. [Lean proofs](../PrimeFactors/HexagonalWeights.lean) · [Search measurements](choosing-hexagonal-radices.md)

## The rounded midpoint and gap

Write the odd factors as $h-d,h+d$, in either order, with $h^2-d^2=N$ and $3|d|\le h$. For a balanced pair define the public integers

$$
l=\lceil\sqrt N\rceil,\qquad u=\lfloor\sqrt{9N/8}\rfloor,\qquad
g=\lfloor\sqrt{N/8}\rfloor,\qquad H=u-l,\qquad G=2g.
$$

The interval search applies when $H>0$. Every feasible point has $l\le h\le u$ and $|d|\le g$. In fact it satisfies the sharper bound

$$|d|\le g-3(u-h).$$

To prove it, expand $(3h-|d|)^2-8N=(h-3|d|)^2\ge0$. Since $8u^2\le9N$, we have $3(3h-|d|)\ge8u$. Also $u<3(g+1)$ by the public square-root bounds. If $3h-|d|\le3u-g-1$, then $3(3h-|d|)\le9u-3g-3<8u$, a contradiction. The same rounded endpoints give $3H\le g$. Indeed $8u\le9l$ follows by squaring, hence $9H\le u<3(g+1)$. [Integer rounding proofs](../PrimeFactors/HexagonalWeights.lean)

## How the corner bound changes the weights

Put $X=|a+b|$ and $Y=|a-b|$. The rectangle gave width $HX+GY$ for the candidate trace. To bound the width on the truncated rectangle, reflect the signs as needed and maximize $X(h-k)+Y(d-e)$ over two feasible points. The gap difference is at most $G-3(u-k)$, and $h\le u$. Thus the trace difference is at most $GY+(X-3Y)(u-k)$. Maximizing over $0\le u-k\le H$ yields

$$W(a,b)=\max\{GY,\ HX+(G-3H)Y\}.$$

For a fixed slope $s$, admissible weights obey $b\equiv sa\pmod R$. Any nonzero pair with $W(a,b)<R^2$ suffices to restrict the trace to at most one integer of the prescribed residue. The new sufficient condition is

$$(G+3H)R^3>4HG^2.$$

The earlier condition was $R^3>4HG$. At the same endpoints the new lower threshold for $R^3$ is strictly smaller whenever $H>0$. Rounding or choosing a smooth radix can give the same integer for the two conditions.

In the signed coordinates $a+b,a-b$ the region $W<1$ is a symmetric hexagon. Its horizontal intercepts are $\pm1/H$. On each boundary line $a-b=\pm1/G$, the horizontal extent is $-3/G$ through $3/G$. Its area is $2/(HG)+6/G^2$. The area gain over the old diamond is $1+3H/G$. The lattice of stationary weights in these coordinates has determinant $2R$. Scaling the hexagon by $R^2$ and applying the planar Minkowski theorem explains the cubic threshold. The following finite proof handles strict inequalities at all integer endpoints. [Mathlib's geometry of numbers](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Group/GeometryOfNumbers.html)

## An exact finite proof

Let $D=G-3H>0$, $m=GR^2$ and $c=DR^2$. In the integer square $0\le i,j<m$, select the half-open diagonal strip $-c\le i-j<c$. The diagonals at gaps $t$ and $t-c$, with $0\le t<c$, have combined length $(m-t)+(m-c+t)=2m-c$. Thus exactly $c(2m-c)=D(G+3H)R^4$ grid points are available.

The earlier parity and remainder encoding, applied with coefficients $HG,DG$, assigns $4HG^2DR$ labels. Under the new sufficient condition two distinct strip points have the same label. Their coordinate differences are

$$
I=HG(a+b)+DG(a-b),\qquad J=HG(a+b)-DG(a-b)
$$

for a nonzero stationary pair $a,b$. Both $|I|$ and $|J|$ are strictly smaller than $m$. The identity $\max(|z+v|,|z-v|)=|z|+|v|$ gives $H|a+b|+D|a-b|<R^2$ after cancelling $G$. The strip also gives $|I-J|<2c$, so $G|a-b|<R^2$ after cancelling $2D$. These are the two required terms of the maximum. The proof establishes existence without constructing or storing the strip. [Integer strip and collision proof](../PrimeFactors/HexagonalWeights.lean) · [Parity encoding](../PrimeFactors/MidpointWeightLattice.lean)

## Which directions have to be tested?

Keep the old two-dimensional Gauss-reduced basis in the original rectangle coordinates. The four directions to test are its two basis vectors, their sum, and their difference. To see why these still suffice, put $z=H|a+b|$, $v=G|a-b|$ and $w=W(a,b)$. The rounded aspect ratio gives $6H\le G$, so $v\le w$ and $2z+v\le2w$. Hence

$$4(z^2+v^2)\le(2w-v)^2+4v^2\le5w^2.$$

The squared Euclidean length in the old transformed lattice is $2(z^2+v^2)$. For any minimizer, $w$ is at most the first basis vector's hexagon score, and that score is at most its Euclidean length. Every minimizer therefore has squared length at most $5/2$ times the first vector's squared length. The existing Gauss lemma shows that squared length below three times that value forces both integer basis coefficients into $\{-1,0,1\}$. Up to sign the four listed possibilities cover every nonzero minimizer. [Four-direction proofs](../PrimeFactors/HexagonalWeights.lean)

## Comparing slopes and sizes

The weaker bound $|d|\le g-k(u-h)$ also holds for $0\le k\le3$. Repeating the area calculation gives the sufficient threshold $4HG^2/(G+kH)$ for $R^3$. Since $H/G$ tends to $(3-\sqrt8)/2$, the limiting radix ratios relative to the rectangle are as follows.

| Gap slope $k$ | Relative cube threshold | Relative radix threshold | Remainder groups at 82 bits | Relative groups on the 2,048-bit comparison |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 1.00000 | 1.00000 | 7,188,480 | 1.00000 |
| 1 | 0.92099 | 0.97294 | 7,096,320 | 0.96610 |
| 2 | 0.85355 | 0.94859 | 6,912,000 | 0.94915 |
| 3 | 0.79532 | 0.92650 | 6,773,760 | 0.93220 |

The last two columns use the existing smooth-radix choice on $\lfloor4HG^2/(G+kH)\rfloor$, then count the exact swap orbits. The group counts require no factor search. The upper endpoint of the continuous arc has derivative $d|d|/dh=h/|d|=3$. Any $k>3$ would cut off part of that arc just inside the endpoint. This proves optimality among these single lines through the endpoint. It leaves open polygons with additional tangents or different shapes.

At 2,048 bits the raw choice at $k=3$ still gives a **677-bit** count of remainder groups. On 34,387, the same policy changes the radix from 18 to 17 and *increases* the group count from four to nine, because their unit groups have different sizes. A lower radix threshold gives more choices of admissible radices. The threshold alone does not order their totients or their end-to-end runtimes. [Benchmark inputs](../benchmarks/midpoint-weights.json) · [Radix and orbit calculations](../experiments/midpoint_weights.py)
