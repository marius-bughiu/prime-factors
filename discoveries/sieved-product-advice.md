# How much a product prefix and suffix can improve a midpoint search

Let $X$ be a power of two. Sample distinct primes $X\le p<q<2X$ uniformly among pairs for which $N=pq\ge2X^2$. This gives factors of the same bit length and products of exactly twice that bit length. A selector sees the known leading and trailing ones of $N$ for free. At each step it may read the next unused bit from either end. Each leaf of this decision tree prescribes moduli $1\le m<X$ and a search depth $B_m$ per modulus. The budget $T$ bounds $\sum_m R(m)B_m$ **at each leaf**, where $R(m)$ counts the square roots of one modulo $m^2$. The subsequent root computations and midpoint tests can use the full product. [Search model and checked cell bound](product-prefix-and-suffix.md)

**Theorem.** Fix $0<\epsilon<1$. If the selector reads at most $(1-\epsilon)\log_2 X$ further bits on every path, the fraction of inputs it recovers is

$$O_\epsilon\!\left(\min\{1,T/\sqrt X\}\right).$$

For any fixed $0<\delta<1/2$ and $1\le T\le X^{1/2-\delta}$, some list already attains $\gg_\delta T/\sqrt X$ without reading any extra bits. Thus menus using this many adaptive prefix and suffix bits have the same optimal order of coverage as prescribed lists in this range. The theorem concerns reserved midpoint slots and is an unconditional asymptotic deduction on paper. Its constants do not give an explicit finite estimate at 2,048 bits. [Finite bound at 2,048 bits](product-prefix-and-suffix.md) · [Prescribed-list lower bound](stride-budget.md)

## The two prime conditions in one leaf

Suppose a path reads $h$ high bits and $k$ low bits in addition to the known ones. The product lies in a half-open interval of width $\Delta=2X^2/2^h$ and in an odd class $a$ modulo $Q=2^{k+1}$. Put $W=X/2^{h+k}$, an integer at least $X^\epsilon$. A hit at $m$ of depth $B\ge1$ forces $(q-p)/2=mc$, with $1\le c\le C=\lfloor2\sqrt{XB}\rfloor$. For each $c$ there are at most $r_Q(a+m^2c^2)$ classes of $p\bmod Q$, where $r_Q(t)$ counts the roots of $z^2\equiv t\pmod Q$. This follows from $z=p+mc$. At a fixed such class choose $0\le u<Q$ and write $p=u+Qn$. The restrictions on $p,q$ and on $p(p+2mc)$ are intervals in increasing $n$. An increase of $QW$ in $p$ increases the product by at least $2XQW\ge\Delta$, so the allowed indices fit in $W$ consecutive integers. [Gap bound](../PrimeFactors/GapStride.lean) · [Finite cell injection](../PrimeFactors/ProductAdvice.lean)

Define $F(v)=\prod_{\ell\mid v,\ \ell>2}(\ell-1)/(\ell-2)$ over prime divisors. The number of possible indices in this class for which both $u+Qn$ and $u+Qn+2mc$ are sample primes is at most

$$O\!\left(\frac{W F(mc)}{(\log W)^2}\right).$$

Here the implied constant is absolute. Take $z=\sqrt W<X$. At each odd prime $\ell\le z$ the two expressions exclude two residue classes of $n$, except when $\ell\mid mc$, when they exclude one. Denote this number by $\nu_\ell$. Indeed $Q$ is a power of two, and both sampled primes are at least $X$, so equality with an excluded prime is impossible. The arithmetic large sieve bounds the count by $(W+3z^2/2)/G$, where $G$ is the sum over odd squarefree $d\le z$ of $\prod_{\ell\mid d}\nu_\ell/(\ell-\nu_\ell)$. Extra missing classes can only increase the sieve denominator. This form follows from bounding the interval denominator $W+3dz/2$ in (1.8) by $W+3z^2/2$. [Montgomery and Vaughan, *The large sieve*, Corollary 1 and (1.7)–(1.8)](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=2)

To bound $G$ uniformly, restrict its primes to $\ell\le y=z^{1/8}$. Without the restriction $d\le z$, the total weight is $E=\prod_{3\le\ell\le y}(1-\nu_\ell/\ell)^{-1}$. Under the distribution obtained by dividing these weights by $E$, a prime $\ell$ occurs in $d$ with probability $\nu_\ell/\ell$. Thus $\mathbb E\log d\le2\sum_{\ell\le y}(\log\ell)/\ell\le4\log y=\tfrac12\log z$. For the second inequality, with $t=\lfloor y\rfloor$, count the multiples of each prime in $\log(t!)$ and use $\lfloor t/\ell\rfloor\ge t/(2\ell)$. Markov's inequality gives $G\ge E/2$. Replacing two excluded classes by one at $\ell\mid mc$ multiplies the Euler factor by $(\ell-2)/(\ell-1)$. For the baseline product, $(1-2/\ell)^{-1}\ge(1-1/\ell)^{-2}$, and the product of $(1-1/\ell)^{-1}$ over odd primes up to $y$ includes the reciprocal sum of all odd integers up to $y$. Hence $G\gg(\log y)^2/F(mc)\gg(\log W)^2/F(mc)$ for large $W$, as required.

## Summing the prime factors of the gap and the singular roots

The required weighted root estimate, uniformly for odd $a$, $m,C\ge1$ and powers of two $Q$, is

$$\sum_{c\le C}F(c)\,\#\{z\bmod Q:z^2\equiv a+m^2c^2\pmod Q\}\ll C+\sqrt Q\log(2C).$$

Expand $F(c)=\sum_{b\mid c}\lambda_b$, where $\lambda_1=1$ and $\lambda_b=\prod_{\ell\mid b}1/(\ell-2)$ for odd squarefree $b$, with zero weight elsewhere. The series $\sum_b\lambda_b/b$ converges by its Euler product. Also $\sum_{b\le C}\lambda_b\ll\log(2C)$. To see the latter without a prime asymptotic, write $b\lambda_b=\prod_{\ell\mid b}(1+2/(\ell-2))$ on its support. Expand and sum $1/b$ over the multiples of each resulting divisor $e$. This costs at most $(1+\log C)\prod_{\ell>2}(1+2/(\ell(\ell-2)))$.

Write $Q=2^v$. The root count for a target $t$ is bounded by $4\sum_{j\le v/2}2^j\mathbf1_{4^j\mid t}$, with $j\ge0$. This includes the zero target. For odd $m$ and $j\ge1$, the condition $4^j\mid a+m^2c^2$ selects at most four classes of $c$ modulo $4^j$. Since $b$ is odd, each such class combines with $b\mid c$ into one class modulo $4^j b$. Summing $\lambda_b(C/(4^jb)+1)$ over $b\le C$ bounds the weighted contribution of any one class by $O(C/4^j+\log(2C))$. The same bound applies to the unconstrained $j=0$ term. Sum the two geometric series with weights $2^j$ to obtain the estimate. When $m$ is even all targets are odd, so at most four roots occur, and $\sum_{c\le C}F(c)\le C\sum_b\lambda_b/b$. [Dyadic root counts](product-prefix-and-suffix.md#singular-roots-and-short-ranges-of-cofactors)

## Returning from leaves to products

We have $Q\le2X^{1-\epsilon}$, $C\ge\sqrt X$, and $\log W\ge\epsilon\log X$. Hence $\sqrt Q\log(2C)\ll_\epsilon C$ uniformly in $B$. For example, $\log(2C)/C$ decreases for $C\ge\sqrt X$ when $X$ is large. Combining the two bounds with $F(mc)\le F(m)F(c)$ gives at most $O_\epsilon(W\sqrt X\,F(m)\sqrt B/(\log X)^2)$ successful pairs for this modulus at this leaf.

For every odd $\ell\mid m$, $(\ell-1)/(\ell-2)\le2$. The two roots $\pm1$ at each odd prime-power component of $m^2$ and the Chinese remainder theorem give $F(m)\le R(m)$, including $m=1$. Thus $\sum_m F(m)\sqrt{B_m}\le T$ per leaf. Each binary split halves $W$, so the leaf sum of $W$ is at most its root value $X$ even with different bit choices and stopping depths. The number of successful pairs is $O_\epsilon(X^{3/2}T/(\log X)^2)$. Both primes in $[\sqrt{2}\,X,2X)$ guarantee the required product width, giving a denominator $\gg X^2/(\log X)^2$ by the prime number theorem. Division proves the upper bound.

For the matching lower bound, use the prescribed prime list from the stride-budget theorem and restrict both primes to $[3X/2,7X/4]$. The interval has length $X/4$, contains $\asymp X/\log X$ primes and always satisfies the product-width condition. Its shorter length preserves the lower count from Cauchy–Schwarz in the bins and can only decrease the overlap upper bounds. The same single-midpoint short-gap count works for $T=1$. Dividing these successful counts by the full conditioned population gives the stated lower order. [List construction and overlap estimates](stride-budget.md#a-list-that-attains-the-bound)
