# How many narrow weighted-sum tests cover the factor range?

On the fresh 2,048-bit example, covering every possible smaller-factor location with weighted sums of width four takes **more than $2^{675}$ tests**. Even if all composite locations are skipped for free, covering the remaining prime locations takes more than $2^{662}$ tests. The product can determine the weights and locations of every test. A search that finds a factor early, or uses other information to discard locations, can avoid completing this cover. [Checked arithmetic for both controls](../PrimeFactors/TraceStripThresholds.lean) · [The interval tests being analyzed](ruling-out-an-interior-interval.md)

## What one test covers

Write $X=\sqrt N$. On the public interval $I=[L,U]$ we have $U=\lfloor X\rfloor$ and $N\le 2L^2$. For positive integers $a,b$ a **strip** tests all locations $x\in I$ whose weighted sum $F_{a,b}(x)=ax+bN/x$ belongs to a chosen closed real interval of length at most four. The two weights and both endpoints can depend on the entire product. A strip can cover two separated intervals of locations. The count below grants the test both intervals in full, including every composite and nonsquare candidate in them.

This model includes the geometric part of a window certified to have at most one parity-compatible sum. A real interval containing at most one integer of a specified parity has length at most four. More generally, if a trace interval contains $t$ such integers, splitting it at those integers gives at most $t+1$ strips, each of width at most two. Thus a cover which charges one setup plus its parity-compatible traces per window is subject to the same lower bound. Extra congruence classes, batch evaluations and eliminations based on other evidence require their own cost analysis. Hiary’s prescribed-center factor search has a classical $N^{1/3+o(1)}$ bit-operation upper bound. The project’s checked schedule uses at most $2^{682}$ window tests for the targets. The lower bound here concerns the number of strips in this particular geometric cover. [Hiary’s paper](https://arxiv.org/abs/1408.2608) · [Checked upper bound](../PrimeFactors/ArbitraryDivisorWindow.lean)

## Packing many strips with the same weights

On the domain, $1\le N/x^2\le 2$. If $a<b$ or $a>2b$, integer spacing gives $|a-bN/x^2|\ge1$ throughout $I$. One strip then contains at most five integer locations. Equivalently, for $x\le y$ the exact difference is $(y-x)(a-bN/(xy))$. Lean checks the latter argument for arbitrary positive real endpoints. This accounts for all positive integer weights, including ratios outside the balanced range. [Off-range bound](../PrimeFactors/TraceStripThresholds.lean)

For one direction with $b\le a\le2b$, suppose $m$ strips use those weights. Order the trace intervals by their left endpoints and clip portions covered by earlier intervals, retaining shared endpoints. At most $m$ intervals of width four or less remain. Take their inverse images and split at the minimum of $F$. On either monotone branch the resulting intervals are ordered and have total trace variation at most $4m$. If $l$ is the sum of all their lengths on both branches, then

$$ b\,l^2\le16Xm. $$

One way to see the gain from combining strips is that $F''(x)=2bN/x^3\ge2b/X$. Moving outward from the minimum, a fixed amount of disjoint horizontal length incurs its least trace variation when it is packed contiguously against the minimum. Integrating the linear lower bound on the outward derivative gives $b\,l_{\rm branch}^2/X\le4m$. Adding both branches gives the displayed bound. An endpoint of $I$ can serve as the anchor if the minimum lies outside $I$. The Lean proof derives the same inequality from exact secants on ordered lists. The conversion of an arbitrary family of real strips into ordered branch intervals is the set-theoretic argument above. At most $2m$ intervals remain, so their integer count is at most $2m+l$. [Per-direction packing theorem](../PrimeFactors/TraceStripPacking.lean)

## Combining different weights

Suppose a cover uses at most $M$ strips. For each occupied in-range pair $(a,b)$, let $m_{a,b}$ and $l_{a,b}$ denote its number of strips and total covered branch length. Put $S=\sum_{(a,b)}1/b$, counting each distinct pair once. Cauchy’s inequality gives

$$\left(\sum l_{a,b}\right)^2\le
   \left(\sum b l_{a,b}^2\right)S\le16XMS.$$

Consequently the count $W$ of covered integer locations obeys $W\le5M+\sum l_{a,b}$. The $5M$ charge includes the rounding at interval endpoints and every out-of-range direction. Overlaps between directions can only reduce the number of distinct locations. [Cross-direction inequality](../PrimeFactors/TraceStripThresholds.lean)

For a dyadic budget $M=2^k$, let $j=\lceil k/2\rceil$ and $B=2^j$. At denominator $b$, at most $b+1$ numerators lie between $b$ and $2b$. Also at most $M$ pairs are used in total. Charging each pair $1/B$ initially gives

$$ S\le {M\over B}+\sum_{b=1}^B(b+1)(1/b-1/B)
       \le {M\over B}+{B\over2}+j+1.$$

The last inequality uses $\sum_{b=1}^{B}1/b\le j+1$, by grouping successive powers of two. Denote this upper bound by $S_0$. If $W>5M$, the four-power test below rules out covering $W$ locations with that budget. It uses integer arithmetic for the budgets in the table.

$$(W-5M)^4>256\,N M^2 S_0^2.$$

When $W$ is a fixed positive fraction of $X$, the bounds $S=O(\sqrt M)$ and $W\le5M+4\sqrt{XMS}$ require $M=\Omega(N^{1/3})$. The choices can be adaptive and different on every product. Lean checks the Cauchy step, the dyadic denominator-price bound for a histogram with the stated caps, and the fourth-power comparison. The passage from arbitrary strip sets to ordered branch intervals, the integer rounding per component, and the construction of the histogram are counting arguments given here. [Denominator sum, Cauchy step and fourth-power comparison](../PrimeFactors/TraceStripThresholds.lean) · [Earlier bound for a particular Farey schedule](farey-work.md)

## The two 2,048-bit controls

Let $Y=2^{1024}$ and use the actual equal-bit-width lower endpoint $L=\max(2^{1023},\lceil N/(Y-1)\rceil)$. The all-integer row sets $W=U-L+1$. For primes alone, Dusart’s Theorem 6.9, inequality (6.6), supplies a conservative lower bound for $\pi(U)-\pi(L)$. Here $\log U-1<709$ and $\log L-1.1>707$. Thus at least $W=\lfloor U/709\rfloor-\lceil L/707\rceil$ of the locations are prime. This count includes every prime location, whatever its gcd with $N$. The analytic prime-count estimate is cited on paper. Lean checks the integer thresholds for both choices of $W$ using the actual products and square roots. The count is unconditional. [Dusart, Theorem 6.9](https://arxiv.org/pdf/1002.0442#page=9) · [Exact thresholds](../PrimeFactors/TraceStripThresholds.lean)

| Locations a completed cover must contain | Fresh product | Crossed product |
| --- | ---: | ---: |
| All integers between the public endpoints | More than $2^{675}$ strips | More than $2^{676}$ strips |
| All primes between the same endpoints | More than $2^{662}$ strips | More than $2^{664}$ strips |

The interval width matters. The broader balance-only interval $[\lceil X/\sqrt2\rceil,\lfloor X\rfloor]$ requires more than $2^{676}$ strips for every 2,048-bit product if all integers must be covered. For this conclusion, the simpler price $S\le3\sqrt M$ follows by summing $2$ per denominator through $\lfloor\sqrt M\rfloor$ and charging the remaining at most $M$ pairs $1/(\lfloor\sqrt M\rfloor+1)$ each. At $M=2^{676}$ the broad interval has $W-5M>(2/7)X$, since $1/\sqrt2<17/24$ and $X\ge2^{1023}$. Then $(2/7)^4 2^{2047}>2304M^3$ contradicts $(W-5M)^4\le2304NM^3$. This uniform statement concerns the broader interval.

For comparison, the equal-bit-width interval can be much shorter. Put $D=2^{512}$ and take $p=Y-75D+1$, $q=Y-1335D+1$. For each $z\in\{p,q\}$, the exact modular check $3^{(z-1)/2}\equiv-1\pmod z$ proves primality. For any prime divisor of $z$ the order of 3 contains $2^{512}$, so that divisor exceeds $\sqrt z$. Their product has 2,048 bits and its public equal-width interval contains fewer than $2^{522}$ integers. Lean certifies the two primes, their exact product with multiplicities, their bit widths and the interval width using the partial-order primality verifier. The integer calculation below reproduces the example. [Checked boundary factorization and width](../PrimeFactors/TraceStripThresholds.lean)

~~~python
from math import isqrt

Y, D = 2**1024, 2**512
p, q = Y - 75*D + 1, Y - 1335*D + 1
assert all(pow(3, (z-1)//2, z) == z-1 for z in (p, q))
n = p*q
lower = max(Y//2, (n+Y-2)//(Y-1))
assert n.bit_length() == 2048 and isqrt(n)-lower+1 < 2**522
~~~
