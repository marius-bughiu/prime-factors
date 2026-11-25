# How the product changes which factor windows we can test

Suppose two 1,024-bit primes multiply to the 2,048-bit number $N$. The smaller prime must be at least $N/2^{1024}$ and at most $\sqrt N$. As the product approaches the largest possible product, those endpoints approach each other. Using the actual $N$ in both the window bound and the endpoints lets us cover the smaller prime with **fewer than $(19/20)2^{509}$ locations**. That is still about $1.6\times10^{153}$ locations at the upper bound. The proof uses a 24,576-row lattice at each location. We have checked the bound in Lean. We have not carried out that search. [Feasible range and proof](../PrimeFactors/FeasibleDivisorCover.lean)

The larger prime gives a second opportunity. It must be at least $\sqrt N$, which makes it easier to force an equation to vanish at its position. The product also turns small shifts near the smaller prime into larger shifts near the larger one. The two effects can offset each other. [Larger-factor proof](../PrimeFactors/CoupledDivisorWindow.lean) · [Reciprocal comparison](../PrimeFactors/ReciprocalDivisorWindow.lean)

## Keeping the product and the divisor bound together

Write $B=2^{1024}$ and take $D=\lceil N/B\rceil$. The earlier calculation used the largest possible $N$ and the smallest possible $D$ separately. Those extremes cannot occur together. The needed inequality contains $N^T$ on the cost side and $D^{mr}$ on the budget side, where $m$ is the multiplicity, $r$ the lattice dimension and $T=m(m+1)/2$. Since $N\le BD$, it suffices to pay $B^T$ and compare the remaining cost with $D^{mr-T}$. Here $D\ge2^{1023}$. For the larger factor we can use $D=\lceil\sqrt N\rceil$ and $N\le D^2$ instead.

| Radius in odd indices | Rows sufficient with independent bounds | Rows sufficient using the product | Rows sufficient targeting the larger factor |
| ---: | ---: | ---: | ---: |
| $2^{500}$ | 51 | 49 | 47 |
| $2^{510}$ | 1,044 | 695 | 417 |
| $2^{511}$ | Estimate fails uniformly | May succeed for particular inputs | 2,093 |

The entries count sufficient dimensions for a uniform first-vector guarantee. At a prescribed center the output is one polynomial with fewer distinct roots than there are rows. The full-band construction at radius $2^{511}$ still takes $2^{510}$ locations. The actual high-dimensional searches have only been bounded on paper and in Lean. Our measured full-size construction used **nine** rows. [Proof of the table](../PrimeFactors/CoupledDivisorWindow.lean) · [Nine-row experiments and cost](wider-windows-and-the-missing-location.md)

For a complete smaller-factor cover, use radius $13\cdot 2^{507}$ below $19\cdot2^{1019}$ and $15\cdot2^{507}$ above. Both use multiplicity 12,287 and dimension 24,576. Counting only odd positions between the public endpoints, including rounding the two window counts upward, yields the bound at the top of this page. The freshly generated and crossed comparison products give about $2^{507.84}$ and $2^{508.71}$ locations respectively. A larger equation carries a much larger per-location cost. These counts compare this project's local covers. Established general-purpose deterministic algorithms have stronger complexity bounds. [Grid definition and count](../PrimeFactors/FeasibleDivisorCover.lean) · [Harvey and Hittmeir](https://arxiv.org/abs/2105.11105)

## One product passes where another fails

There is an exact threshold for the particular LLL height estimate we use. Choose rational bounds $a/s$ for $\log_2 N$ from above and $b/s$ for $\log_2 D$ from below, with $0<b\le a$ and positive integer $s$. For a power-of-two radius $W$, set $c=s(2\log_2 W+1)$. **Some** degree $k$ and multiplicity $1\le m\le k$ make the estimate succeed for those rational parameters if and only if

$$2b^2>ac.$$

The proof keeps the full dimension penalty. Necessity follows by completing a square. For sufficiency take $k=at$ and $m=bt$. The strict margin gives a gain proportional to $t^2$, whereas the extra dimension penalty grows on the order of $t\log t$. Lean supplies a finite choice of $t$. This is a test of a sufficient height estimate applicable before reduction. Failure at a chosen floor still allows shorter individual lattice vectors, higher floors farther along the range and other algorithms. [Threshold and constructive proof](../PrimeFactors/DivisorWindowThreshold.lean)

We evaluated both directions on the actual public integers, with $D=\lceil N/B\rceil$ and $W=2^{511}$. On the fresh input, dimension 2,577 and multiplicity 1,288 already pass. On the crossed input **every** dimension and admissible multiplicity fails the same estimate at that floor. For the successful case we rounded the input bounds conservatively; for the failed case we rounded optimistically. Both conclusions use integer sixteenth powers, checked in Lean. No hidden factors were used. [Both checked examples](../PrimeFactors/DivisorWindowThreshold.lean)

## What changes when the two factors trade places?

For this comparison, the normalized cost is the determinant of the coefficient-scaled lattice divided by $D^{m(k+1)}$, with $D$ the divisor floor being used. At a reference value $X$ let $Y=N/X$. A displacement near $X$ corresponds to a displacement about $Y/X$ times as large near $Y$. In the determinant estimate, replacing $(X,W,m)$ by $(Y,WY/X,k-m)$ at the same degree $k$ leaves its normalized cost **exactly equal**. For a finite interval $[A,B]$, the reciprocal interval has width $(B-A)N/(AB)$. When we use the lower endpoints as divisor bounds on both sides, the change in twice the logarithm of the normalized cost is exactly

$$\log(B/A)\,(k-2m)(k+1).$$

These formulas compare intervals before rounding to odd indices. Lattice reduction time and the actual coefficients can still differ between the two locations. [Lean identities](../PrimeFactors/ReciprocalDivisorWindow.lean)

## How precise would a clue have to be?

The Riemann repository's zero-free Euler-factor argument led to an earlier question about the boundary value $B(1)$ of the principal Dirichlet L-function. For an odd product $N=pq$ with $p<q\le2p$, its normalized reading determines a cosine of $\delta=(\log q-\log p)/2$. Our present question is how accurately that value would have to be supplied to choose a single interval. [Definition and prior decoder](reading-the-boundary.md) · [Source of the analytic question](../docs/research.md#what-the-riemann-hypothesis-gives-a-factor-search)

Suppose the supplied approximation certifies a lower bound $a\ge 1/8$ for $\delta$. An absolute error at most $2^{-574}$ suffices to choose one radius-$2^{453}$ interval for the larger prime. With the 2,093-row bound, error at most $2^{-516}$ suffices to choose one radius-$2^{511}$ interval. The cosine becomes flat near equal factors, where that lower bound on the gap need not hold. An alternative valid across the balanced range uses 1,232 adaptive readings of error at most $1/5$, at heights below $2^{513}$, to select one interval of the latter size.

In each case the reading is **additional information**. The proof selects the center without knowing the primes once the readings are supplied. It gives no efficient way to compute those readings from $N$ alone. The interval and decoding results use the finite Euler factors and unconditional mathematics. [Formal bounds, center and conditional root theorem](../PrimeFactors/AnalyticDivisorWindow.lean)
