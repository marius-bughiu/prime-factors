# How much can failed square tests rule out when we choose their locations freely?

Even if the product and all earlier results guide every choice, $2^{32}$ individual weighted square tests cover fewer than $2^{552}$ possible locations for the smaller factor of a 2,048-bit product. In the central product range studied here, there are at least $2^{1021}$ locations allowed by the bit lengths alone. Thus less than one part in $2^{469}$ can be excluded by the intervals around those tests. The bound allows every multiplier from 1 through the input and all factorizations of each multiplier. Earlier bounds required the tests to begin near the minimum possible weighted sum. Here they can be placed anywhere. [Checked geometry and complement](../PrimeFactors/DisplacedTraceCoverage.lean) · [Earlier prefix bound](sharing-square-tests-across-factor-ranges.md)

## What one test tells us

Let $N=pq$, where $p$ is the smaller prime. Choose positive weights $ab=k$ and consider $F(x)=ax+bN/x$ for $0<x\le\sqrt N$. If $x=p$, then $F(p)$ is the integer $ap+bq$, and the discriminant $F(p)^2-4kN$ equals $(ap-bq)^2$. Testing one integer $z$ for that square can cover a whole range of smaller-factor positions. For example, if the true trace has to be in a known set of residue classes modulo 24, positions with $F(x)$ strictly between the previous and next admitted integers force $F(p)=z$ whenever $x=p$. A failed test excludes those positions. The tested value $z$ is itself admissible, so the preceding and following admitted integers are each within 24 of it. [Lehman's original weighted-square construction](https://doi.org/10.1090/S0025-5718-1974-0340163-2) · [Hart's one-line method](https://doi.org/10.1017/S1446788712000146)

Now allow any closed trace band of width $W$, starting at any real height. Suppose $x\le y$ are both in its preimage, on the same side of the minimum of $F$. Then

$$\sqrt{k}(y-x)^2\le W\sqrt N.$$

On the rising side, $bN\le ax^2$ implies $a\ge b$ and $F(y)-F(x)\ge a(y-x)^2/y$. On the falling side, $ay^2\le bN$ implies $F(x)-F(y)\ge(bN/y^2)(y-x)^2/x$. There $bN/y^2$ is at least both $a$ and $b$. Either expression yields the bound because $x,y\le\sqrt N$. Thus a single branch spans at most $N^{1/4}\sqrt W/k^{1/4}$ units in factor coordinates. The exponent has a simple witness. For $k=1$, the ordinary trace band $[2\sqrt N,2\sqrt N+1]$ contains the traces of every real position between $\sqrt N-N^{1/4}/2$ and $\sqrt N$ when $N\ge16$. [Proofs of both bounds](../PrimeFactors/DisplacedTraceCoverage.lean)

## Adding up the exclusions

Each ordered factorization $ab=k$ contributes at most two branches. An interval of length $d$ contains at most $1+d$ integers. Using the project's finite divisor estimate $\tau(k)<9k^{1/4}$, the union over *every* allocation contains at most

$$2\tau(k)+18N^{1/4}\sqrt W$$

integer positions. For $k\le N$, a transcript of bands with widths $W_i$ therefore reaches at most $18N^{1/4}\sum_i(1+\sqrt{W_i})$ positions. The multipliers and starting heights may differ on every row. This proof applies to the actual transcript selected for a product, with no independence assumption. [Divisor estimate](../PrimeFactors/MultiplierDivisorReach.lean) · [Arbitrary-band and transcript theorems](../PrimeFactors/DisplacedTraceCoverage.lean)

For single labels on any period-24 wheel we grant width 49 per test. Since $N^{1/4}\le 2^{512}$, any such $T$ tests cover at most $144\cdot2^{512}T$ positions. Set $U=2^{1024}$. When $9U^2/16\le N\le5U^2/8$, every integer from $5U/8+1$ through $3U/4$ could have a partner within the bit-width limits. Covering even half this block by these brackets requires more than $2^{500}$ tests. The formula with a user-supplied candidate set applies outside this product range as well. A successful test could still identify both factors immediately.

The conclusion also survives eliminating every composite candidate first. Write $A=5U/8$ and $B=3U/4$. Dusart's published unconditional estimates give $B\le710\pi(B)$ and $700\pi(A)\le A$. It follows that this block contains more than $2^{1011}$ **prime** candidate locations. The same $2^{32}$ tests can remove fewer than $2^{552}$ even if all their reached positions are prime. The Lean proof takes Dusart's two published inequalities at $A,B$ as explicit premises, checks the logarithms and constants, and proves the finite count. These candidate primes need only meet the bit-width limits for this product. [Dusart, equation (6.6)](https://arxiv.org/pdf/1002.0442#page=9) · [Endpoint and prime-survivor proofs](../PrimeFactors/DisplacedTraceCoverage.lean)

## Can many modular failures eliminate further residue classes?

Suppose a sieve reports that each tested discriminant $z_i^2-4a_i b_i N$ is nonsquare modulo a common modulus $m$. Choose *any* invertible candidate residue $x$ modulo $m$ and set $y=N/x$ there. This single partner fits the public product and every reported failure simultaneously. For every row the true candidate trace has discriminant $(a_i x-b_i y)^2$, so its trace automatically avoids the failed label. Thus these modular failures, even taken together, leave every invertible smaller-factor class locally possible. The proof works over any commutative ring. The numerical values of the discriminants contain additional information beyond their failure flags. On $2,100,271$, three individually nonsquare remainders multiplied to a square and led to the factors $1,283$ and $1,637$. This is one concrete way correlations can help. [Simultaneous local-survival theorem](../PrimeFactors/DisplacedTraceCoverage.lean) · [Checked three-remainder example](testing-three-weighted-remainders.md)
