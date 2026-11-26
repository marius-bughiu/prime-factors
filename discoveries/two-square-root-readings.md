# Can two square roots tell us where to look?

Read the first **177 binary digits after the point** in each of $\sqrt N$ and $\sqrt{2N}$. For every possible combination of those 354 bits, the outer of the project's two factor-sum windows remains more likely. Always picking the outer window therefore attains the highest prediction accuracy possible from those two words. The result concerns a uniform draw from distinct 1,024-bit primes $p<q$ whose product has 2,048 bits. It is unconditional. A factorization method using the exact integer remainders or further information from $N$ has a different input. [Definition and size of the windows](where-to-look-for-the-factor-sum.md) · [Earlier result for one 300-bit reading](what-the-square-root-reveals-about-the-gap.md)

Put $X=2^{1023}$. The eligible pairs have $X<p<q<2X$ and $pq\ge2X^2$. Write $T$ for their number, $P$ for the number of primes in the band, and $G,J$ for the counts in the central and outer windows. The central condition is $q^3\le4X^2p$. To obtain either reading using the product alone, compute $\lfloor\sqrt{2^{354}u}\rfloor-2^{177}\lfloor\sqrt u\rfloor$ for $u=N,2N$ using integer square roots. Both readings are irrational before rounding. The odd prime $p$ has exponent one in both radicands, and subtracting an integer preserves irrationality. Thus none of the points lie on a dyadic boundary. [Endpoint proof](../PrimeFactors/JointSquareRootPhase.lean)

## The nonzero frequencies

For either region $R$ and real $\alpha>0$, write $S_R(\alpha)=\sum_{(p,q)\in R}\exp(2\pi i\alpha\sqrt{pq})$. The frequency for a pair of integer indices $h,k$ is $h+\sqrt2 k$. Its negative gives the complex conjugate of the same sum; throughout the bounds use $\alpha=|h+\sqrt2 k|$.

Take $M=\lceil\alpha\rceil$ consecutive blocks of smaller-prime positions, each of size at most $\lceil X/M\rceil$. Here $M<X$ for all frequencies used below. Within each block apply Cauchy–Schwarz to its sum over the $P$ possible larger primes, then enlarge the sum of squared absolute values to all integer positions for the larger prime. For fixed $p,p'$, the permitted common partners lie in an interval because the width, ordering, product and central-or-outer conditions give interval bounds on $q$. If $p\ne p'$, the absolute derivative of $\alpha(\sqrt p-\sqrt{p'})\sqrt q$ throughout that interval lies between $\alpha|p-p'|/(8X)$ and $1/4$, since $|p-p'|<X/M$. It varies monotonically. The first-derivative inequality bounds the corresponding integer sum by $8X/(\alpha|p-p'|)$, with the sign removed by conjugation if necessary. Summing reciprocals of the differences in both directions, adding the diagonal, and applying Cauchy–Schwarz across the blocks gives

$$
 \frac{|S_R(\alpha)|}{P\sqrt X}
 \le \sqrt{M(1+C/\alpha)},\qquad C=16(1+\log X)<11376.
$$

Primality enters through $P$ and the outer Cauchy–Schwarz step. All off-diagonal first-derivative estimates concern sums over consecutive integers. [Block calculation for one root](what-the-square-root-reveals-about-the-gap.md#cancellation-across-prime-pairs) · [Arias de Reyna, Lemma 1](https://arxiv.org/pdf/2002.05982#page=2)

For $\alpha\ge1$, use $M\le\alpha+1$ and $M/\alpha\le2$. The displayed bound is at most $\sqrt{|h|}+(6/5)\sqrt{|k|}+152$, using $2^{1/4}<6/5$. For $0<\alpha<1$, we must allow near-cancellation between $h$ and $\sqrt2 k$. Then $k\ne0$, there are at most two $h$ for this $k$, and $|k|\le |h|<\sqrt2|k|+1$. Since $h^2-2k^2$ is a nonzero integer,

$$
 \alpha^{-1}\le |h-\sqrt2 k|\le |h|+\sqrt2|k|<4|k|.
$$

It follows from $M=1$ that the near-cancelling frequency contributes at most $214\sqrt{|k|}$ in units of $P\sqrt X$. This use of the conjugate frequency also rules out a second zero mode. [Checked conjugate-frequency inequality](../PrimeFactors/JointSquareRootPhase.lean)

## Fourier bounds for small rectangles

Both observed cells have width $d=2^{-177}$. For each interval take Vaaler's trigonometric majorant $A_i$ and minorant $B_i$, of degree $H=2^{208}$. They have means $d+e,d-e$ with $e=1/(H+1)$. At every nonzero frequency $|h|\le H$ the absolute Fourier coefficient of either polynomial is bounded by

$$
 a(h)=\min(d,1/(3|h|))+1/H,\qquad a(0)=d+1/H.
$$

Indeed the oscillatory part is bounded by $|\sin(\pi h d)|/(\pi|h|)$ and the correction by $1/(H+1)$. Open, closed and half-open versions of each interval include the same input points because all endpoint values are rational. The Vaaler estimate applies without RH. [Vaaler, *Some extremal functions in Fourier analysis*, §8](https://doi.org/10.1090/S0273-0979-1985-15349-2) · [Bourgain, Cochrane, Paulhus and Pinner, proof of Theorem 10.1 and equation (10.1)](https://www.impan.pl/shop/en/publication/transaction/download/product/83005#page=24)

For the rectangle indicator, an upper polynomial is $A_1A_2$ and a lower polynomial is $B_1A_2+A_1B_2-A_1A_2$. To see the lower inequality, write $x,y$ for the two indicators. Then $(A_1-x)(A_2-y)\ge0$, $A_2\ge0$, and $A_1\ge0$. The upper mean exceeds $d^2$ by $2de+e^2$. The lower mean falls short by $2de+3e^2$. Each of the three polynomial products has coefficient envelope $a(h)a(k)$ at every nonzero pair $(h,k)$, including pairs with exactly one index zero. [Formal tensor bounds and constant coefficients](../PrimeFactors/JointSquareRootPhase.lean)

Write $A=\sum_{|h|\le H}a(h)$ and $F=\sum_{|h|\le H}a(h)\sqrt{|h|}$. Splitting the first sum at $1/d$ gives $A\le5+(2/3)\log(Hd)<20$. For the second, $\sum_{j=1}^H j^{-1/2}\le2\sqrt H$ and $\sum_{j=1}^H\sqrt j\le H\sqrt H$ give $F\le(10/3)\sqrt H$. For each of the three products, the large-frequency contribution divided by $P\sqrt X$ is at most $FA+(6/5)AF+152 A^2$. For the near-cancelling pairs, $a(h)a(k)\le4/|k|^2$. Accounting for both signs of $k$, at most two $h$ per $k$, and $\sum_{j\ge1}j^{-3/2}\le3$, their total contribution is at most $16\cdot214\cdot3<15000$. Together the two estimates give $148\sqrt H+80000$ per product.

## From counts to predictions

For $R$ of size $n_R$, let $c_R$ count the pairs giving a specified rectangle. The constant and nonconstant coefficients give

$$
 |c_R-d^2 n_R|\le(2de+3e^2)n_R+3(148\sqrt H+80000)P\sqrt X.
$$

The established unconditional normalization is $XP<41056T$. Use $n_R\le T$, $e<2^{-208}$ and $\sqrt X>2^{511}$. Relative to $d^2T$ the count error is less than

$$
 \frac {2}{2^{31}}+\frac {3}{2^{62}}+
 \frac{3\cdot41056(148\cdot 2^{104}+80000)2^{354}}{2^{511}}
 <2.956\times10^{-9}<2^{-28}.
$$

Apply this estimate separately to the central and outer counts. The finite count-to-fraction inequality gives positive population in each cell and places its central fraction within $2^{-28}$ of $G/(G+J)$. The established unconditional upper bound for that fraction is $0.49999999383$, so the outer window wins in every cell. Shortening either word groups cells with the same strict majority. The new Lean module checks the tensor inequalities, the conjugate-frequency bound, the endpoint argument, the normalization and the conditional decision given the region estimates. The bilinear and Fourier estimates above are paper deductions. [Finite proof](../PrimeFactors/JointSquareRootPhase.lean) · [Population normalization](../PrimeFactors/SquareRootPhasePopulation.lean) · [Global window proportions and analytic assumptions](what-the-square-root-reveals-about-the-gap.md#removing-the-rh-assumption-from-the-decision)

The width calculation also gives an asymptotic rule. For a fixed $0<\eta<1/5$ take at most $\eta\log_2 X$ fractional bits in each root. At that finest resolution choose $H=\lceil d^{-1}(\log X)^4\rceil$. The relative constant-term error is $O((\log X)^{-4})$, the envelope mass is $O(\log\log X)$, and the weighted first moment is $O(\sqrt H)$. The elementary block argument has $C=O(\log X)$, and the prime number theorem gives $XP/T=O(\log X)$. Therefore the relative error from nonzero frequencies is $O(X^{-1/2+(5/2)\eta}(\log X)^4)$, uniformly in the chosen cell. Both errors are smaller in order than the established outer-window advantage of order $(\log X)^{-2}$. The two equally sized readings can thus contain almost $(2/5)\log_2 X$ fractional bits in total while preserving the decision on every cell for all sufficiently large $X$. [Global asymptotic and its hypotheses](what-the-square-root-reveals-about-the-gap.md#what-changes-as-the-primes-get-larger)
