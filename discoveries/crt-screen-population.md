# How small can the closest square quotient be?

Draw two 1,024-bit primes independently and uniformly, then condition on their being distinct and their product having 2,048 bits. From that product $N$ alone choose the **first 32 odd primes** at which $N$ is a nonzero square. Write $D$ for their product. Even if we check every integer $t\ge0$ and every sign choice in the CRT construction, the chance that **any** integer quotient $(t^2-N)/D^2$ has absolute value below $2^{900}$ is less than $2^{-60}$. The probability concerns this choice of modulus. A method can still combine larger quotients or choose its moduli differently. The 992-bit minimum in our full-size example is a measurement on one product. [Experiment and search cost](crt-square-norms.md) · [Different bound for a direct square split](crt-square-gaps.md)

This estimate accounts for choosing $D$ after reading $N$. Treating the 32 primes as fixed beforehand would miss that dependency. The finite bound is unconditional. Lean checks the local count, the stopping-weight inequality, the window estimate, the subset double count, and the final arithmetic. The steps connecting them to the prime population below are a paper argument. [Lean lemmas and constants](../PrimeFactors/CRTScreenCount.lean)

## Counting the products on which the screen stops early

Write $X=2^{1023}$, $r=32$, $Y=2^{900}-1$ and $W=2Y+1$. Number the odd primes in increasing order as $\ell_1,\ell_2,\ldots$. In the proof, first consider the $J=256$ primes through 1621. Consider a possible screening history that stops at its $r$th success within these $J$ tests. It fixes $D$. For each $t$ a hit with small quotient must have the form $N=t^2-D^2Q$ with $-Y\le Q\le Y$. Since $N<4X^2$ and $D^2Y\le1621^{64}Y<X^2$, there are fewer than or equal to $3X$ nonnegative choices for $t$.

At a skipped prime $\ell$, $N$ must be a quadratic nonresidue. Both input primes exceed 1621. For each fixed $t$, the map $Q\mapsto t^2-D^2Q$ permutes residues modulo $\ell$, since $\ell\nmid D$. Exactly $(\ell-1)/2$ classes give a nonresidue. For any $s$ skipped primes of product $M$, CRT therefore retains at most $M/2^s$ classes of $Q$. Covering the $W$ consecutive choices by full periods bounds their count by $(W+M)/2^s$. This uses arithmetic progressions in the unknown quotient, without an independence assumption about primes.

In each history keep just the first $h=104$ skips, or every skip if there are fewer. Their product is at most $B=\prod_{i=r+1}^{r+h}\ell_i$, since at most $r$ successful tests could precede any retained skip. When all skips are kept, the sum of weights $2^{-s}$ over stopped histories is at most $2^r$. To see this, let $F(j,k)$ be the total weight with $j$ tests left and $k$ successes still needed. Then $F(j,0)=1$, $F(0,k)=0$ for $k>0$, and $F(j+1,k+1)=F(j,k)+F(j,k+1)/2$. Induction gives $F(j,k)\le2^k$. For histories having more than $h$ skips we can instead count all $\binom Jr$ possible selected subsets with weight $2^{-h}$. Consequently the number of candidate products is at most
$$3X(W+B)\left(2^r+\binom Jr2^{-h}\right).$$
Each candidate product accounts for at most two ordered pairs of distinct primes.

## Bounding the chance that the 32nd prime comes later

A pair with fewer than 32 successes among the first 256 primes skips at least $J-r+1=225$ of them. It therefore contributes at least $\binom{225}{99}$ incidences with sets of 99 skipped primes. Conversely fix one such set, of product $m$, and fix the first prime $p$. The sign conditions on its partner $q$ allow at most $m/2^{99}$ residues modulo $m$, since $p$ is a unit. There are at most $(X+m)/2^{99}$ integer partners in $[X,2X)$. Taking $T=\prod_{i=158}^{256}\ell_i$ bounds $m$ for all $\binom{256}{99}$ subsets. This counts even the late cases in which no useful quotient ever occurs.

The earlier explicit prime estimates give fewer than $1.511X/\log X$ choices for $p$ and more than $(0.22X/\log X)^2$ eligible ordered pairs. Use $\log X<710$. After division by the population size, the two contributions are bounded by
$$
U=\frac{6(W+B)710^2}{0.22^2X}\left(2^{32}+\frac{\binom{256}{32}}{2^{104}}\right),
\qquad
V=\frac{1.511\cdot710}{0.22^2}\left(1+\frac{T}{X}\right)
\frac{\binom{256}{99}}{2^{99}\binom{225}{99}}.
$$
The cleared-denominator comparison gives $U+V<2^{-60}$. This includes any continuation past 1621. When a small-prime screening divisor is itself encountered after that point, it too is covered by the late-case bound. [Population constants and primary source](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)

## What changes as the bit length grows?

Let $b=\log_2 X$ and sample distinct primes in $[X,2X)$, optionally retaining only products at least $2X^2$. For fixed $0<\epsilon,\delta<1$, allow up to $r\le b^{1-\delta}$ selected primes and set $Y=X^{1-\epsilon}$ (rounded down). For the first-$r$ rule the probability of such a small quotient is at most **$X^{-\min(\epsilon,2/3)+o(1)}$ unconditionally**. The following estimates are paper deductions. Applying the finite incidence argument directly already gives
$$X^{-\epsilon+o(1)}+\exp\big(-\Omega_\epsilon(\log X/\log\log X)\big).$$

Indeed take $J=\lceil b\rceil$. The prime number theorem gives $\ell_J=O(b\log b)$. Take $h=\lfloor c_\epsilon b/\log_2 b\rfloor$ for a sufficiently small positive constant $c_\epsilon$, so every $h$-prime period is smaller than both $Y$ and $X$. We have $D^2Y<X^2$ for large $X$, since $r\log\ell_J=o(b)$. The term $\binom Jr/2^h$ tends to zero because $r\log J=o(h)$. The earlier stopped histories thus cost at most $X^{-\epsilon+o(1)}$ of the population. For the late histories take subsets of $h$ skips. The ratio $\binom Jh/\binom{J-r+1}h$ is $\exp(O(rh/J))=\exp(o(h))$ by its product formula. The incidence bound contributes at most $O(\log X)2^{-h+o(h)}$.

### An unconditional power saving for the late cases

Choose a fixed $A>1$ and increase the number of tests in the proof to $J=\lceil b^A\rceil$. The early-stopping argument still gives $X^{-\epsilon+o(1)}$. Indeed $\log\ell_J=(A+o(1))\log b$, so $h=\lfloor c_{\epsilon,A} b/\log_2 b\rfloor$ still bounds each retained period by $Y$, and $r\log J=o(h)$ still pays for all the stopped histories.

Write $\chi_j$ for the quadratic character modulo $\ell_j$. Set $S(u,v)=\sum_{j=1}^{J}\chi_j(u)\chi_j(v)$. For an eligible prime pair with fewer than $r$ successes, every character value is nonzero since $\ell_J<X$. At least $J-r+1$ terms have sign $-1$, so $|S(p,q)|\ge J-2r$. For any positive integer $m$, count these pairs by summing $S(u,v)^{2m}/(J-2r)^{2m}$ over **all integer pairs** in the interval. The majorant is nonnegative, so the extra pairs and any zero character values on them preserve the upper bound. The denominator of the desired probability, even with the product-size condition, is $\gg X^2/(\log X)^2$.

In the expanded moment each ordered tuple of $2m$ prime indices contributes the square of $\sum_{X\le u<2X}\prod_{a=1}^{2m}\chi_{j_a}(u)$. If each index occurs an even number of times, the sum counts at most $X+1$ integers. Pairing positions with matching indices and choosing an index for each pair gives at most $(2mJ)^m$ such tuples. Otherwise let $f>1$ be the product of primes appearing an odd number of times, and $E$ the product of the other distinct primes present. The tuple character equals the primitive quadratic character modulo $f$ multiplied by $\mathbf 1_{(u,E)=1}$. Primitivity follows by CRT from that of each local Legendre character. Expanding the indicator over the divisors of $E$ gives at most $2^m$ interval sums of the primitive character, each bounded by $O(\sqrt f\log(2f))$ by Pólya–Vinogradov. This accounts for both repetitions and zero values. [Frolenkov, *Numerically explicit version of the Pólya–Vinogradov inequality*](https://arxiv.org/abs/1107.0381)

Take $m=\lfloor\alpha\log X/(A\log b)\rfloor$ for a fixed $0<\alpha<1$, where $\log$ denotes the natural logarithm. Then $f\le\ell_J^{2m}=X^{2\alpha+o(1)}$ and $2^m=X^{o(1)}$. Also $(1-2r/J)^{-2m}=X^{o(1)}$. After normalization, the even-multiplicity tuples cost at most $(2m/J)^m X^{o(1)}=X^{-\alpha(1-1/A)+o(1)}$. The other tuples cost at most $X^{-2+2\alpha+o(1)}$, since their number is at most $J^{2m}$. With $\alpha=2/(3-1/A)$, both exponents give the same saving. Taking $A$ arbitrarily large shows that the log of the late probability divided by $\log X$ has limit superior at most $-2/3$. This yields the stated unconditional exponent together with the early bound.

Even without Pólya–Vinogradov, every nonprincipal tuple character has zero sum over its full period of length at most $\ell_J^{2m}$. Bounding the incomplete period by its length changes the second term to $X^{-2+4\alpha+o(1)}$. Choosing $\alpha=2/(5-1/A)$ gives an elementary late-case saving with limiting exponent $2/5$.

### The Dirichlet hypothesis

The Dirichlet hypothesis from the RH verification sharpens the whole bound to **$X^{-\epsilon+o(1)}$**. Return to $J=\lceil b\rceil$. For an exact word of $J$ prescribed signs of $pq$, expand its indicator as a product of $J$ factors $(1\pm\chi_\ell(pq))/2$. Summing over both primes turns each nonprincipal term into a square of a prime character sum. Every nonempty product of the local Legendre characters is nonprincipal by CRT. The common modulus $M=\prod_{i\le J}\ell_i$ has $\log M=O(b\log b)$. The GRH character estimate and partial summation bound each nonprincipal prime sum by $\sqrt X$ times a fixed polynomial in $b$. If $P$ is the number of primes in the interval, a word therefore contributes at most $P^2/2^J+X^{1+o(1)}$ ordered pairs, including the diagonal. Fewer than $r$ positive signs give at most $\sum_{i<r}\binom Ji=X^{o(1)}$ words. Dividing by the eligible population bounds the late probability by $X^{-1+o(1)}$. The analytic estimate improves the exponent for $\epsilon>2/3$. Computing either hidden factor remains a separate problem. [Montgomery and Vaughan, Theorem 13.7](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/17.0_pp_419_451_Conditional_estimates.pdf) · [Dirichlet theorem verification record](https://math.mit.edu/~drew/grh/)
