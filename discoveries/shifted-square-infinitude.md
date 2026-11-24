# Infinitely many balanced examples with a large prime gap

There are infinitely many pairs of primes $p<q<2p$ with $(2p+1)(2q+1)$ a square and $q-p>p/90$. Given only $N=pq$, the shifted-square formula recovers these primes with two integer square roots. Ordinary Fermat search requires order $\sqrt N$ consecutive midpoint tests on the same inputs. The infinitude is a paper application of a published prime-tuple theorem. Lean verifies the factor-recovery formula. [Lean proof](../PrimeFactors/DiscriminantPencil.lean) · [Formula and its input assumptions](square-collision-density.md#a-family-with-a-product-only-formula)

## Fifty fixed linear forms

Take the 50 odd integers $u=251,253,\ldots,349$. For a positive integer $t$ set
$$
L_u(t)=u^2t+(u^2-1)/2.
$$
Then $2L_u(t)+1=(2t+1)u^2$. Any two prime values at the same $t$ have the shifted-square property because the product of the two shifted values is exactly $((2t+1)uv)^2$.

These integer linear forms are admissible. For each odd prime $\ell$, choose a residue $t$ with $2t+1\equiv0\pmod\ell$. Every $L_u(t)$ is then $-1/2\bmod\ell$. For $\ell=2$, take odd $t$ since $u^2\equiv1\pmod8$. Thus no prime divides the product of the forms for every $t$. Each form is primitive, since a divisor of both $u^2$ and $(u^2-1)/2$ divides 1. Distinct forms are nonproportional, since the determinant for $u,v$ equals $(v^2-u^2)/2$.

Kim's Lemma 2.1 gives an unconditional lower bound $\gg X/(\log X)^{50}$ for the number of positive $t$ at which at least two of these forms are prime, with every form bounded by $X$. The implied constant may depend on the 50 forms. Each such $t$ supplies a pair $p=L_u(t)<L_v(t)=q$. For $t\ge1$, the ratio is
$$
\frac qp=\frac{v^2(2t+1)-1}{u^2(2t+1)-1}
>\frac{v^2}{u^2}\ge\frac{349^2}{347^2}>1+\frac1{90}.
$$
It is less than 2 because $349^2+1<2\cdot251^2$. A fixed index pair $(u,v)$ can give any specified product at most once since $L_u(t)L_v(t)$ is strictly increasing. Thus there are also $\gg X/(\log X)^{50}$ distinct such products with $q\le X$, after allowing multiplicity at most $\binom{50}{2}$. Some fixed pair of indices recurs infinitely often. The proof does not identify which pair. [S. Kim, Lemma 2.1](https://www.csun.edu/~sungjin/SJK_Totient2-3%281%29.pdf#page=4)

For distinct odd primes, Fermat's first successful midpoint is $h=(p+q)/2$. There are $h-\lceil\sqrt N\rceil+1$ tests from the ceiling square root, and
$$
h-\sqrt N=\frac{(q-p)^2}{2(\sqrt q+\sqrt p)^2}.
$$
The displayed ratio bounds put this difference between positive constant multiples of $\sqrt N$. The shifted-square formula recovers $h=m(m+1)-N$ for $m=\lceil\sqrt N\rceil$. This work comparison concerns consecutive Fermat midpoints. A finite list of known slope pairs also allows a search tailored to that list. The shifted-square formula uses none of those slopes.

## Prescribing the bit width

For every sufficiently large integer $b$, there are examples with both factors exactly $b$ bits and their product exactly $2b$ bits, with a fixed positive lower bound on $(q-p)/p$. Maynard's Theorem 3.4 supplies a fixed tuple size $k$ for two prime values in an interval $[x,x+y]$, where $x^{7/12+\varepsilon}\le y\le x$. Use $\varepsilon=1/12$, take $U=100k+1$, and use the $k$ odd integers $u=U,U+2,\ldots,U+2(k-1)<1.02U$. The same proof gives admissibility, and all the coefficients are fixed as $b$ grows. [J. Maynard, Theorem 3.4](https://arxiv.org/pdf/1405.2593#page=3)

Choose $x=4\cdot 2^b/(5U^2)$ and $y=x/20$. For sufficiently large $b$, this is in the theorem's range. Throughout the interval all the forms satisfy
$$
0.8\cdot 2^b\le L_u(t)\le (1.02)^2(1.05)(0.8)\cdot2^b+O(U^2)<0.9\cdot2^b.
$$
The resulting factors and their product therefore have the claimed bit widths. Distinct $u$ are separated by at least two, so $q/p>(1+2/(1.02U))^2>1$ uniformly in $b$. Maynard's lower bound gives $\gg 2^b/b^k$ good parameters $t$ in this interval. This asymptotic deduction gives no explicit starting bit width. The repository's 2048-bit example has an independent, finite factorization certificate.

## Counting products at each scale

For every sufficiently large $X$ there are at least $cX/(\log X)^2$ distinct products of primes $X\le p<q\le2X$ on which the shifted-square formula succeeds and $q-p\ge c'X/\log X$, for absolute positive constants $c,c'$. The upper bound $O(X\log X)$ from counting all shifted pairs with common squarefree part applies even without a gap condition. Thus the exponent in the number of successful products is exactly one, up to logarithmic factors, while the entire box contains order $X^2/(\log X)^2$ products. The following deduction uses the unconditional Siegel–Walfisz theorem for primes in progressions. Its asymptotic estimates are on paper. [A proof of the uniform prime-number theorem and its Siegel–Walfisz corollary](https://arxiv.org/abs/2108.10878)

Put $Y=\lceil(\log X)^4\rceil$. Use odd integers $m\in[Y,2Y]$ with $m/\varphi(m)\le C$, for a large absolute constant $C$. There are $\gg Y$ such integers. Indeed $m/\varphi(m)=\sum_{d\mid m}\mu^2(d)/\varphi(d)$ has bounded mean by the convergent product $\prod_\ell(1+1/(\ell(\ell-1)))$ over primes. Summing through $2Y$ and choosing $C$ large excludes fewer than half of the odd integers in this interval.

1. Count the incidences $m^2\mid 2p+1$ for primes $X\le p\le2X$. Each $m$ defines one reduced residue class. Siegel–Walfisz gives order $X/(\varphi(m^2)\log X)$ primes in it, uniformly for these $m$. Their total incidence count is $\gg X/(Y\log X)$. For two allowed moduli $m,l$, the simultaneous condition uses the single reduced class modulo $[m,l]^2$, where brackets denote the least common multiple. The same theorem applies uniformly, since even the squared least common multiple is $O((\log X)^{16})$. The estimate is $O(X/([m,l]^2\log X))$ because $[m,l]/\varphi([m,l])\le C^2$.
2. Summing the intersection estimates gives $O(X/(Y\log X))$. Indeed for $g=\gcd(m,l)$ there are at most $(2Y/g)^2$ ordered pairs and $1/[m,l]^2\le g^2/Y^4$. Summing this over $g\le2Y$ gives $O(1/Y)$. By Cauchy–Schwarz the number $M$ of distinct primes occurring is $\gg X/(Y\log X)$.
3. Group those primes by the squarefree part $d$ of $2p+1$. The divisibility condition puts $d\le(4X+1)/Y^2$, giving at most $D=O(X/Y^2)$ classes. In one class write $2p+1=dt^2$. Consecutive possible values of $p$ in the box differ by at least a constant times $\sqrt{dX}$, since $dt^2\ge2X$. Thus the number within distance $H$ of any member, including that member, is at most $C_d=1+O(H/\sqrt{dX})$. Summing the capacities gives $O(D+H/Y)$ because $\sum_{d\le D}d^{-1/2}\le 2\sqrt D$.
4. Take $H=c'X/\log X$ with $c'$ small enough that the total capacity is below $M/2$. In a class of $s$ elements at least $s(s-C_d)_+$ ordered pairs have distance greater than $H$, where $(x)_+=\max(0,x)$. Counting over the classes and applying Cauchy–Schwarz gives at least $(M-\sum C_d)^2/D$ ordered pairs. Dividing by two gives the claimed bound. Unique prime factorization makes the resulting products distinct. [Lean finite counting inequality](../PrimeFactors/SeparatedPairs.lean)

For the upper bound, sum $(1+O(\sqrt{X/d}))^2$ over $d\le4X+1$, allowing composite factors as well. This gives $O(X\log X)$. The fixed-relative-gap construction above also has $X^{1+o(1)}$ successful products when its bound through $X$ is used. Neither counting argument supplies an effective 2048-bit density estimate.
