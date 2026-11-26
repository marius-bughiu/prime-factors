# Can the fractional part of the square root locate the factor sum?

On small products, a square root whose fractional part is above one half looks like a clue that the two primes are close. The clue fades as the numbers grow. On 34,893,133 products of 18-bit primes it predicted the correct search window 50.50% of the time. On 65,536 freshly drawn 64-bit products it was correct 49.95% of the time.

For the project's population of 2,048-bit products, we obtain a stronger conclusion. Even with the **first 300 bits after the binary point in the square root**, the outer search window remains more likely for *every* possible reading. For this two-way prediction, always choosing the outer window achieves the best population accuracy attainable from those bits. Its advantage over an even guess is tiny. This result is unconditional. The argument combines a prime-count estimate, an exponential-sum bound and finite arithmetic checked in Lean. [Search windows and input distribution](where-to-look-for-the-factor-sum.md) · [Phase transfer](../PrimeFactors/SquareRootPhasePopulation.lean) · [Prime-count error transfer](../PrimeFactors/QuantileThetaBounds.lean)

## The public reading

Draw distinct 1,024-bit primes $p<q$ uniformly among pairs with $N=pq$ of exactly 2,048 bits. Set $X=2^{1023}$ and $B=2X$. The central window contains the true sum precisely when $q^3\le B^2p$. Denote that event by $G$ and its complement by $J$.

Write $r=\lfloor\sqrt N\rfloor$ and $x=\sqrt N-r$. The first $m$ binary digits of $x$ can be computed exactly as $\lfloor\sqrt{2^{2m}N}\rfloor-2^m r$. Another public reading, the scaled integer remainder $y=(N-r^2)/(2r+1)$, satisfies
$$y=x-\frac{x(1-x)}{2r+1},\qquad 0\le x-y<1/(8X).$$
Its high bit agrees with the high bit of $x$ on integer nonsquares: both are high exactly when $N-r^2\ge r+1$. The small correction matters when comparing much finer intervals.

There is an arithmetic reason to investigate the high reading. Set $s=(p+q)/2$ and $d=(q-p)/2$. Then $N=s^2-d^2$. If $0<d^2\le s-1$, the square root lies strictly between $s-1/2$ and $s$. These particular products always have a high reading, and the first Fermat square test already factors them.

## Cancellation across prime pairs

Let $P$ denote the number of primes in $[X,2X)$ and $T$ the number of eligible sorted pairs. For $R$ equal to $G$, $J$ or the full eligible region, the partners of each fixed $p$ form an interval intersected with the primes. Write $e(z)=\exp(2\pi i z)$. For $1\le h\le X$ the following bound holds:
$$\left|\sum_{(p,q)\in R}e(h\sqrt{pq})\right|
 \le P\sqrt{X\bigl(h+16(1+\log X)\bigr)}.$$

Divide the $X$ integer positions for $p$ into $h$ consecutive blocks of size at most $\lceil X/h\rceil$. For one block with $P_j$ primes, apply Cauchy–Schwarz to the outer sum over prime $q$, then enlarge the sum of squared absolute values to all integer $q$ in the band. The diagonal contributes at most $XP_j$ inside that last sum. For distinct $p,p'$ in the block, the eligible $q$ values lie in the intersection of two intervals. The phase there is $h(\sqrt p-\sqrt{p'})\sqrt q$. Its derivative has monotone absolute value between $h|p-p'|/(8X)$ and $1/4$. The upper bound uses the fact that the two indices differ by less than $X/h$. The first-derivative inequality of Kuzmin and Landau therefore bounds the off-diagonal sum by $8X/(h|p-p'|)$. Summing the harmonic series in both directions bounds the square of the block contribution by $P P_j X[1+16(1+\log X)/h]$. Finally, $\sum_j\sqrt{P_j}\le\sqrt{hP}$. This proves the displayed inequality for each of the three regions without any prime-distribution hypothesis. [Arias de Reyna, Lemma 1 and Landau's constant](https://arxiv.org/pdf/2002.05982#page=2)

Apply the interval form of Erdős–Turán with cutoff $H=2^{329}$. Its count error is at most $\#R/(H+1)+3\sum_{h=1}^{H}|S_R(h)|/h$. The Vaaler majorant and minorant give these constants since the contribution of the two frequencies at $h$ is at most $2(1/(\pi h)+1/(H+1))<3/h$. Inserting the exponential-sum bound uses $\sum_{h\le H}h^{-1/2}\le2\sqrt H$ and $\sum_{h\le H}1/h\le1+\log H$. The project has the finite bound $XP<41056T$: the product of all primes in the band divides $\binom{2X}{X}\le2^{2X}$, and the earlier Lean count gives $X^2<21000000T$. Consequently the error divided by $T$ is at most
$$2^{-329}+6\cdot41056\,2^{-347}+3\cdot41056\cdot25000\,2^{-511}<2^{-328}.$$
Here $\sqrt{16(1+\log X)}(1+\log H)<25000$. This establishes an absolute count error for any one phase interval for each region. [Bourgain, Cochrane, Paulhus and Pinner, proof of Theorem 10.1](https://www.impan.pl/shop/en/publication/transaction/download/product/83005#page=24) · [Finite population and numerical bound](../PrimeFactors/SquareRootPhasePopulation.lean)

For a phase interval of width $2^{-300}$ the central and outer counts accordingly differ from $2^{-300}\#G$ and $2^{-300}\#J$ by less than $2^{-328}T$ each. The interval has positive population. Dividing the two counts shows its central fraction differs from the unconditional central fraction by less than $2^{-28}$. The scaled remainder has the same bound with an additional allowance of $2^{-726}$: to compare intervals, expand or contract one end of the corresponding $x$ interval by $1/(8X)$, then divide by the cell width. The reasoning concerns these rounded observations. A rule that performs another calculation on the full product can have different information.

## Removing the RH assumption from the decision

On the factor band, Axler's Proposition 1.1 gives $|\vartheta(t)-t|<0.024334\,t/\log^3t$ unconditionally. Partial summation on any $[u,v]\subseteq[X,2X]$ bounds the error between its prime count and $\int_u^v dt/\log t$ by
$$\epsilon\le0.024334\bigl(4X/709^4+X/709^5\bigr)+2.$$
The first term bounds the two endpoints, the integral uses $v-u\le X$, and two extra units cover arbitrary endpoint conventions. In the notation of the window analysis, $\epsilon/X<3.85338\times10^{-13}$. Replacing the two measures in turn changes the central population fraction by less than $1.79070\times10^{-9}$. [Axler, Proposition 1.1 and equation (1.7)](https://arxiv.org/pdf/2203.05917#page=1) · [Two-measure derivation](where-to-look-for-the-factor-sum.md#a-finite-population-estimate-at-2048-bits)

There is a genuine smooth bias toward the outer window. For $n=N/B^2$, put $A=\log(1/\sqrt n)$ and $\lambda=A/\log\sqrt N$. The central deficit below $1/2$ on that fiber is at least $(1-\lambda^2)\lambda^2/8$. Split $[1/2,11/16]$ into three equal bins. Their lower bounds for $A$ are $0.28,0.23,0.18$ respectively. Each bin's area is at least its lower bound times $B^2/16$, whereas the total eligible area is $(1-\log 2)B^2/4<31B^2/400$. Accounting for the band’s density ratio, the mean smooth deficit exceeds $7.9666\times10^{-9}$. Combining this with Axler and the earlier smooth upper bound gives an unconditional central fraction between **0.49999996837 and 0.49999999383**. Even the largest allowed change after observing the 300 bits is smaller than this bias. This proves the claim for every reading, including the scaled-remainder version. The external analytic inequalities and the block cancellation argument are written deductions. Lean checks the finite population normalization, count-to-fraction transfer and numerical implications.

## What changes as the primes get larger?

The same calculation gives a size law for independent primes of $b$ bits, conditioned on a full $2b$-bit product. Set $B=2^b$, $L=\log B$ and $A(n)=-\tfrac12\log n$. As $b\to\infty$, the central probability is
$$\frac12-\frac{C}{L^2}+O(L^{-3}),\qquad
C=\frac{\int_{1/2}^1 A(n)^3\,dn}{8\int_{1/2}^1 A(n)\,dn}>0.$$
Indeed the smooth density on each fiber gives $\operatorname{atanh}(\lambda/2)/\operatorname{atanh}(\lambda)=1/2-\lambda^2/8+O(\lambda^4)$, uniformly for $\lambda=A/(L-A)$. The fiber mass is proportional to $A L^{-2}(1+O(1/L))$. Integrating gives the coefficient above. Axler's theta estimate bounds the prime-count error on each section by $O(B/L^4)$ and the error in the resulting population fraction by $O(L^{-3})$. The leading term thus survives for actual prime pairs.

For the square-root reading, taking $H$ of order $X^{1/3}$ in the exponential-sum estimate makes the count error relative to the entire population $O(X^{-1/3}\log X)$. Here $P$ is of order $X/\log X$ and $T$ of order $X^2/\log^2X$. Conditioning on one cell of $m$ fractional bits costs a factor $2^m$. For each fixed $0<\eta<1/3$, all $m\le(1/3-\eta)b$ therefore give a conditional error $o(1/L^2)$. **For every sufficiently large width, the outer window is more likely in every such cell.** This is an asymptotic statement proved by the estimates above. The separate finite calculation specifies 300 usable bits at the particular width requested.

## Checks at smaller widths

The direction of the test was fixed before measurement: a high remainder predicts the central window. Exhaustive counts include every distinct eligible sorted pair at each factor width from 5 through 18. The larger sample retains the first 65,536 eligible 32-bit-prime draws under a separate fixed seed.

| Bits per prime | Eligible pairs | Correct predictions |
| ---: | ---: | ---: |
| 10 | 1,718 | 57.92% |
| 12 | 19,546 | 53.52% |
| 14 | 228,713 | 52.05% |
| 16 | 2,753,877 | 51.01% |
| 18 | 34,893,133 | 50.50% |
| 32 (sampled) | 65,536 | 49.95% |

At 32 bits the rule was correct 32,738 times. Always choosing the central window was correct on 50.13% of that sample. A 95% Wilson interval for the rule's accuracy under independent sampling is 49.57% to 50.34%. The target-size conclusion comes from the analytic bounds. All four counts per width and the sampling recipe can be reproduced independently. [Complete census](../research/sqrt-remainder-census.json) · [Generator and replay command](../experiments/sqrt_remainder_census.py)
