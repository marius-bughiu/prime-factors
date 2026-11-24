# What a near-square probe says about the factor gap

Let $N=pq$ for distinct primes $X\le p<q<2X$. Write $H=(p+q)/2$ and $D=(q-p)/2$. An integer $s$ near $\sqrt N$ gives a small, public residual $s^2-N$. Any divisor $m$ of this residual comes with a known square root $s\bmod m$ of $N$. The question is how often one of these *product-dependent* choices also divides the hidden $D$ and brings $H$ into reach of the squared-stride midpoint test. A second probe using $\sqrt{N/d}$ gives an exact positive result when the totient lies in a prescribed square class.

## A residual that finds the factors

Take $N=103469711$. Its integer square root is $s=10172$, and $N-s^2=127$ is prime. This supplies the modulus directly. To lift its known root to modulus $m^2$, write $e=(N-s^2)/m$ and solve $2st\equiv e\pmod m$. Then $(s+mt)^2\equiv N\pmod{m^2}$. For any odd prime $m$ coprime to $N$, the two signs of this lift give every root. One extended Euclidean computation and two midpoint tests suffice after such a prime is identified. Here $(2s)^{-1}\equiv90\pmod{127}$, and the first representatives above $10173$ are $21602$ and $10656$. The latter gives $10656^2-N=3175^2$, so the prime factors are $7481$ and $13831$. Consecutive Fermat search reaches that midpoint after 483 increments. [Lean lift and example](../PrimeFactors/DiscriminantStride.lean) · [Squared-stride criterion](smooth-factor-gaps.md)

## Coverage even when every residual divisor is supplied

Fix a probe radius $1\le A\le X$ and a positive integer depth $B$. Allow **every** positive integer $s$ with $|s-\sqrt N|\le A$. For each $s$, supply the search with **all** positive divisors $m$ of $|s^2-N|$ for free, including composite ones. For each such $m$, try the first $B$ representatives at or above $\lceil\sqrt N\rceil$ of every root class modulo $m^2$. Among uniformly sampled distinct unordered prime pairs in the interval, the proportion recovered is at most

$$A\sqrt B\,X^{-1/2+o(1)}.$$

For $A,B$ bounded by fixed powers of $\log X$, the proportion of pairs covered by this entire union is **$X^{-1/2+o(1)}$**. Thus even unlimited access to factorizations of these particular residuals preserves the same exponent of coverage as one ordinary Fermat midpoint. The bound applies to selecting a subset of these divisors adaptively. It allows an arbitrary amount of work to choose that subset, and counts a split only when one of the indicated midpoints gives the proper factorization. [Coverage of one ordinary midpoint](gap-search-frequency.md) · [Prescribed lists and budgets](stride-budget.md)

On a hit, $D=mc$ with $1\le c<2\sqrt{XB}$ by the midpoint inequality. Also $1\le m\le D<X$ and $s^2-N=me$ for a nonzero integer $e$. The residual has magnitude at most $5AX$ because $\sqrt N<2X$ and $s\le3X$. Subtracting two squares gives

$$(H-s)(H+s)=m(mc^2-e).$$

For fixed $m,c,e$, let $K$ denote the right side. If $K\ne0$, the positive integer $H+s$ divides $|K|$ and determines $H-s$ by exact division. These recover $H,s$ and hence $p,q$. For triples with a solution, $|K|=|H^2-s^2|\le9X^2$. The divisor bound gives at most $X^{o(1)}$ possibilities uniformly. An elementary proof bounds each prime-power contribution $j+1$ to the divisor count by $\ell^{\eta j}$ for $\ell\ge2^{1/\eta}$. The finitely many smaller primes multiply this by a constant depending on $\eta$. [Lean finite injection into divisors](../PrimeFactors/DiscriminantStride.lean) · [Divisor bound, Lemma 30](https://terrytao.wordpress.com/2014/11/23/254a-notes-1-elementary-multiplicative-number-theory/)

The number of possible nonzero $e$ for each $m$ is at most $10AX/m$. Summing over $m\le X$ and the $O(\sqrt{XB})$ values of $c$ gives $A\sqrt B\,X^{3/2+o(1)}$ pairs. If $K=0$, then $H=s$ and $D^2=s^2-N\le5AX$. There are $O(X\sqrt{AX})$ such pairs even counting composite factors. Divide by the prime-pair population, of order $X^2/(\log X)^2$. For the lower bound in the polylogarithmic regime, $m=1$ is always supplied and the first ordinary Fermat midpoint covers $\gg X^{-1/2}$ of the pairs. The counting is on paper. Lean checks the factorization identity, the divisor-count injection and the necessary gap inequality. [Midpoint inequality](../PrimeFactors/GapStride.lean)

For prime $m$ the loss can be made explicitly polylogarithmic. As $m\mid D$ and $m\mid s^2-N$, we have $s\equiv\pm H\pmod m$. Choose $h=(H\pm s)/m$. Then

$$s^2-N=m\left(m(c^2+h^2)-2Hh\right).$$

The case $h=0$ again gives $H=s$. Otherwise $1\le |h|\le5X/m$. For each $m,c,h$ the possible $H$ occupy an interval of length at most $5AX/(m|h|)$. Once $H$ is fixed, so are $D,p,q$. Summing $1+5AX/(m|h|)$ over both signs of $h$, then $m\le X$, and then $c<2\sqrt{XB}$ gives $O(A\sqrt B\,X^{3/2}(\log X)^2)$ candidate pairs. Thus the prime-modulus coverage is $O(A\sqrt B(\log X)^4/\sqrt X)$. [Lean orientation and diameter theorems](../PrimeFactors/DiscriminantStride.lean)

## A scaled square root that determines both factors

Suppose $2<p<q\le 2p$ and $(p-1)(q-1)=d y^2$ for a positive integer $d$. Given $d$ and the product, the following values are exact:

$$y=\begin{cases}\lfloor\sqrt N\rfloor-1,& d=1,\\[2pt]\lfloor\sqrt{\lfloor N/d\rfloor}\rfloor,& d\ge2,\end{cases}\qquad S=N+1-dy^2=p+q.$$

Compute $S$ and test that $S^2-4N$ is a nonnegative square yielding a proper factor pair. Enumerating $1\le d\le L$ costs $O(L\,\operatorname{polylog}N)$ bit operations for $L\le N$, and covers every input whose totient has squarefree part at most $L$. No factorization of the totient is needed to run these trials. Earlier work studied the proximity of $\sqrt{\varphi(N)}$ and $\sqrt N$ under a small-gap condition. Here the extra information is a square class, which can hold at a fixed relative factor gap. [Lean sum decoder](../PrimeFactors/DiscriminantStride.lean) · [Mukhamadiyev et al., square-root proximity](https://doi.org/10.3390/math14101784)

Put $a=p-1$, $b=q-1$. Then $a\le b\le2a+1\le3a$. For $d\ge2$, $(a+b)^2\le6ab\le4d ab=(2dy)^2$. Consequently $0\le N-dy^2=a+b+1<d(2y+1)$, which identifies the integer square root. For $d=1$, $2y\le a+b$ and $a\le y$ imply $(y+1)^2\le N<(y+2)^2$. These inequalities and exact recovery of $S$ are kernel checked. The example $N=1604108860967$ gives $y=517060$ at $d=6$, $S=2599368$, and primes $1008017,1591351$. Their four signed gcds are $2,8,6,2$, and the first successful ordinary Fermat midpoint is 33149 increments beyond its start. [Checked example](../PrimeFactors/DiscriminantStride.lean)

### A 2048-bit product recovered at the sixth scale

Take $p=2(945719\cdot3^{310})^2+1$ and $q=3(575009\cdot2^{492})^2+1$. These are 1024-bit primes, with $q$ about 38.76% larger than $p$. Their totient is six times a square. The four numbers $\gcd(p\pm1,q\pm1)$ are $6,2,4,2$ in lexicographic sign order. Testing six scales from the decimal product recovers both primes. Stopping after five leaves the product unresolved, as does testing all six on the previous power-of-five gap fixture. We chose smooth prime predecessors to make the separate primality certificates inexpensive. The proof of the formula imposes no smoothness requirement. [Decimal inputs and controls](../benchmarks/predecessor-square.json) · [Product-only search](../experiments/predecessor_square.py)

For fixed $L$ this is a sparse promise. In fact the number of integer pairs $1\le a,b\le2X$ with squarefree part of $ab$ at most $L$ is $O(X\log(2X)\sqrt L\log(2L))$. Write $a=gu,b=gv$ with $g=\gcd(a,b)$. The coprime $u,v$ have forms $d_1 x^2,d_2 z^2$ with $d_1d_2=d\le L$. At fixed $g,d_1,d_2$ the number of positive $x,z$ is at most $2X/(g\sqrt d)$. Sum first over $g\le2X$ and then use $\sum_{d\le L}\tau(d)/\sqrt d\ll\sqrt L\log(2L)$ by summing over divisor pairs. For polylogarithmic $L$, even before imposing primality this gives only $X^{1+o(1)}$ possibilities, versus $X^{2-o(1)}$ prime pairs in the population.

The promise $d=1$ nevertheless occurs at fixed relative separation for infinitely many prime pairs. Apply Kim's Lemma 2.1 to the 50 forms $j^2t+1$, $200\le j\le249$. Their determinants are nonzero and setting $t=0$ makes every form a unit modulo every prime, so the tuple is admissible. There are $\gg X/(\log X)^{50}$ parameters giving two primes at most $X$. Their ratio is below $(249/200)^2<2$ and is bounded away from one uniformly for positive $t$, since the fixed coefficients are distinct. Their predecessor product is a square. Each pair of indices yields a specified product at most once, so the same order of lower bound holds for distinct products with $q\le X$. This count uses a varying common parameter and makes no lower-density assertion for the particular small-gcd example. [Sungjin Kim, Lemma 2.1](https://www.csun.edu/~sungjin/SJK_Totient2-3%281%29.pdf#page=4)

A later result allows error in the square relation. It includes an infinite family with unbounded squarefree part and an explicit finite list of corrections. [Noisy square classes](approximate-totient-squares.md) · [Near-square family](near-square-families.md)
