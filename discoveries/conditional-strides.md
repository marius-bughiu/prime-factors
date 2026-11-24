# Choosing a stride from the observed product residue

A search may read the complete residue $a=N\bmod Q$ and use a different list of strides and depths for **every** value of $a$. For a binary word, this extra choice can improve coverage on finite inputs. In the balanced prime-pair model it still obeys the same order bound as a prescribed list when the word is shorter than half the factor width by a fixed proportion.

Sample distinct primes $X\le p<q<2X$ uniformly, let $N=pq$, and prescribe $Q$ before sampling. In cell $a$, an entry $(m,B)$ tests the first $B$ integer midpoints from $\lceil\sqrt N\rceil$ in every square-root class of $N\bmod m^2$, with $1\le m<X$. Reserve at most $T$ slots **per cell**, charging $R(m)B$ where $R(m)$ is the number of square roots of one modulo $m^2$. The list, including its depths, may be any function of $a$. For $Q\le X^{1/2-\epsilon}$ and fixed $0<\epsilon<1/2$, the unconditional success probability is at most

$$
 O_\epsilon\!\left(\min\left\{1,\frac{T}{\sqrt X}E(Q)\right\}\right),
 \qquad E(Q)=\prod_{\substack{\ell\mid Q\\\ell\ \mathrm{odd\ prime}}}
 \left(1+\frac1{2(\ell-1)}\right).
$$

All overlap between $m$ and $Q$ is allowed. For $Q=2^k$, $E(Q)=1$ exactly. A fixed list already achieves $\gg_\eta T/\sqrt X$ for $T\le X^{1/2-\eta}$, so the binary-word upper bound has the right order throughout this range. [Prescribed-list lower bound](stride-budget.md) · [Lean compatibility, root counts and averaging](../PrimeFactors/ConditionalStride.lean)

## Counting one entry in one cell

A hit implies $m\mid(q-p)/2$ and $q-p<4m\sqrt{XB}$ by the midpoint identity. Write $d=2m$, $g=\gcd(d,Q)$, $L=\operatorname{lcm}(d,Q)$ and $h=4m\sqrt{XB}$. For fixed $p$, the conditions $q\equiv p\bmod d$ and $pq\equiv a\bmod Q$ are compatible precisely when $p^2\equiv a\bmod g$. Then $q$ occupies a single reduced class modulo $L$. Let $r_g(a)$ count the unit roots of $a\bmod g$, including $r_1(a)=1$. The two totient denominators combine exactly as $\varphi(g)\varphi(L)=\varphi(d)\varphi(Q)$. Lean checks both identities for arbitrary positive moduli. [CRT proof](../PrimeFactors/ConditionalStride.lean) · [Necessary gap estimate](../PrimeFactors/GapStride.lean)

Put $\alpha=\log Q/\log X<1/2$. Brun–Titchmarsh on length $X$ bounds the first primes in each eligible class modulo $g$ by $2X/(\varphi(g)\log(X/g))$. Its second application bounds partners of each $p$ by $2h/(\varphi(L)\log(h/L))$. Here $g\le Q$ and $h/L=2g\sqrt{XB}/Q$, so the logarithms are at least $(1-\alpha)\log X$ and $(1/2-\alpha)\log X$. The number of successful pairs from this entry in this cell is at most

$$
 \frac{16X^{3/2}}{(1-\alpha)(1/2-\alpha)(\log X)^2}
 \frac{r_g(a)\,m\,\sqrt B}{\varphi(2m)\varphi(Q)} .
$$

Entries with zero depth contribute zero. This counts the *joint* event of seeing $a$ and finding the factors. It requires no assumption about how products are distributed among the cells. [Montgomery and Vaughan, Theorem 2](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3)

## What shared primes reveal

Define $W_Q(a)$ as the product of $\ell/(\ell-1)$ over the odd primes $\ell\mid Q$ for which $a$ is a square modulo $\ell$. The local root counts give

$$
 r_g(a)\,\frac{m}{\varphi(2m)}\le R(m)W_Q(a).
$$

Indeed $m/\varphi(2m)$ is the product of $\ell/(\ell-1)$ over the **odd** primes dividing $m$. An odd prime dividing $m$ but absent from $Q$ reserves two root slots, enough to pay its entire factor. At a shared odd prime there are zero roots if $a$ is a nonresidue, and two if $a$ is a unit square. Each first-digit root lifts uniquely because twice the root is a unit. In the latter case the two roots consume the two reserved slots, leaving the factor $\ell/(\ell-1)$ in $W_Q(a)$. For the dyadic component, if $2^v\parallel m$ with $v\ge1$, then $v_2(g)\le v+1\le2v$. At positive precisions the roots of one modulo $2^j$ number one for $j=1$, two for $j=2$ and four for $j\ge3$. For an odd root $x$, one of $x-1,x+1$ has valuation exactly one, so $x\equiv\pm1\bmod 2^{j-1}$ for $j\ge3$, and all four lifts work. A nonempty unit square fiber is a translate of these roots. If $m$ is odd, the dyadic part of $g$ is at most two and contributes one root. [Lean proof of the four-root upper bound](../PrimeFactors/ConditionalStride.lean) · [Odd-prime lifting](../PrimeFactors/PrimePowerCount.lean)

Use $\sqrt B\le B$ and the per-cell slot cap. Summing the joint upper bound over cells introduces $\varphi(Q)^{-1}\sum_{a\in(\mathbb Z/Q)^\times} W_Q(a)$. Under this *arithmetic average* the square indicators at the distinct odd primes are independent and each has mean $1/2$, by CRT and the equal fibers of reduction on units. The mean is exactly $E(Q)$. The earlier bound already counted the true sampled primes, so this averaging step does not substitute a uniform residue model for the sampling distribution. Divide by the $\asymp X^2/(\log X)^2$ unordered sampled pairs. Lean checks the exact mean over the entire unit group of $Q$. [Finite averaging theorem](../PrimeFactors/ConditionalStride.lean)

The penalty grows slowly even for a product of many small primes. Each local factor divided by $(1-1/\ell)^{-1/2}$ has square $1+1/(4\ell(\ell-1))$. Summing $1/(n(n-1))$ for $n\ge3$ shows $E(Q)\le e^{1/16}\sqrt{Q/\varphi(Q)}$. In particular $E(Q)=O(\sqrt{\log\log(3Q)})$ by the standard totient estimate. The upper bound does not establish sharpness of this extra factor for varying odd $Q$. [Rosser and Schoenfeld, Theorem 15](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)

## Exactly 2048 bits and a finite gain

Set $X=2^{1023}$ and condition the population on $pq$ having exactly 2048 bits. It has at least $\tfrac12(0.22X/\log X)^2$ unordered pairs by the explicit prime bounds for $[\sqrt2X,2X)$. For $Q=2^{500}$ the preceding numerator estimate gives an upper bound of $2^{17}T/\sqrt X$, since $32/[0.22^2(1-500/1023)(1/2-500/1023)]<2^{17}$. Thus **even after reading the 500 low bits of the product**, $2^{40}$ reserved midpoint tests per residue cover less than a $2^{-454}$ proportion of this population. Implementing a function with $2^{500}$ possible inputs could itself be expensive. This upper bound grants the selection for free. [Explicit population denominator](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)

At smaller widths the residue can make a real difference. For prime pairs in $[128,256)$, read $N\bmod3$. On residue one, make one test per root at $m=3$. Otherwise make two consecutive Fermat tests. This covers **210 of 253 pairs**, compared with **168** for the best prescribed two-slot list. Two ordinary tests attain 168. Every $m\ge2$ reserves at least two slots and can be eligible on at most 123 of the pairs just from $m\mid(q-p)/2$. The finite computation and all these counts are kernel checked. [Two-slot regression](../PrimeFactors/ConditionalStride.lean)

## Conditioning on the actual observed word

The stated bound averages over inputs. The Dirichlet result from the RH release also supports a claim about each individual word. Write $P$ for the number of primes in $[X,2X)$ and $A_\chi$ for the sum of $\chi(p)$ over that interval. Under Dirichlet GRH the nonprincipal sums satisfy $|A_\chi|\ll\sqrt X\log(QX)$. Character orthogonality gives the number of ordered distinct pairs in a particular unit cell $a$ as

$$
 \frac{P^2}{\varphi(Q)}+O\!\left(X\log^2(QX)+P\right).
$$

The principal character gives the main term, the other terms are $\overline{\chi(a)}A_\chi^2/\varphi(Q)$ and removing the diagonal costs at most $P$. For $Q\le X^{1/2-\epsilon}$ the error is uniformly smaller than the main term by a factor tending to zero. Dividing the single-cell bound by half this count gives conditional coverage $O_\epsilon(TW_Q(a)/\sqrt X)$ for **each** unit $a$. This is a paper application of the analytic character estimate. [Dirichlet proof verification](https://math.mit.edu/~drew/grh/) · [Taheri and Saleh, Lemma 4.1](https://arxiv.org/pdf/2611.19610#page=5)

Above the stated range, the second Brun–Titchmarsh logarithm can become small. If $Q>4X^2$, the observation can specify the entire product. For instance, on the positive proportion of pairs whose half-gap has a prime divisor $m\equiv3\bmod4$ between $\sqrt X$ and $X^{3/4}$, an unrestricted selection function could factor the now known product and choose that $m$, reserving two midpoint tests. This shows why a bound based only on $Q/\varphi(Q)$ cannot hold for all $Q$, even prime $Q$. It gives no fast way to implement that selection. Feedback from test results, other observed functions of $N$, and changes to the starting midpoint require separate arguments. [Positive-proportion divisor event](gap-search-frequency.md#positive-coverage-from-a-wider-range)
