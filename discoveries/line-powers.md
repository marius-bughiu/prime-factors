# Combining both shifts of a product

We recovered both primes of a specially constructed 2,048-bit number from its product alone. The primes were chosen so that **one part of the smaller prime plus one divides the larger prime minus one, and the rest divides the larger prime plus one**. Using both relationships together produced a factor on the thirteenth trial. Each relationship by itself missed on the same thirteen trials. For two independently chosen 1,024-bit primes, the probability estimate below explains why extending this particular search is unlikely to help. [Benchmark and exact primes](../benchmarks/line-powers.json)

## A public calculation

Write $N=pq$ for two distinct odd primes. Use the Dickson polynomials with $D_0(x)=2$, $D_1(x)=x$ and $D_{k+2}(x)=xD_{k+1}(x)-D_k(x)$. For each label $x$, compute $D_d(x)$ modulo $N$ at the public degree $d=N^2-1$. A proper $\gcd(D_d(x)-2,N)$ splits the product. Binary doubling evaluates the polynomial in $O(\log N)$ modular operations per label. Starting from $(D_1,D_2)$, the next adjacent pair uses $D_{2k}=D_k^2-2$, $D_{2k+1}=D_kD_{k+1}-x$ and $D_{2k+2}=D_{k+1}^2-2$. This is the Lucas arithmetic used in Williams’s $p+1$ method. The choice of degree combines both shifts of the input, since $N^2-1=(N-1)(N+1)$. The earlier signed-period search selects a single shift using a Jacobi symbol. [Williams](https://doi.org/10.1090/S0025-5718-1982-0658227-7) · [Signed periods](jacobi-separation.md) · [Implementation](../experiments/line_powers.py)

Modulo an odd prime $r$ dividing $N$, a label $x$ has the form $z+z^{-1}$. The roots of $Z^2-xZ+1$ either lie in the multiplicative group of the prime field, of order $r-1$, or in the norm-one group in its quadratic extension, of order $r+1$. In the second case Frobenius exchanges the roots. Both groups are cyclic. The trace identity gives $D_d(x)=z^d+z^{-d}$, which equals 2 exactly when $z^d=1$. The two groups meet at $z=\pm1$. Counting the copies of these two elements separately gives two lifts per label and $2r$ lifts in total. Thus the probability of a hit at a uniform label is

$$H_r(d)=\frac{\gcd(d,r-1)+\gcd(d,r+1)}{2r}.$$

For a uniform label modulo $N$, the Chinese remainder theorem makes the hits at $p$ and $q$ independent. The probability of a proper split is $H_p+H_q-2H_pH_q$. If $p+1\mid q^2-1$ then $p+1\mid d$ since $p\equiv-1\pmod{p+1}$, so $H_p\ge 1/2$. If neither $q-1$ nor $q+1$ divides $d$, each of its gcds is at most half the group order, so $H_q\le1/2$. This gives a split with probability at least $1/2$ on every product satisfying these conditions, or at most two independent uniform labels in expectation. This expectation concerns random labels. The benchmark scans consecutive labels. [Lean identities](../PrimeFactors/LinePower.lean)

## A reproducible 2,048-bit example

Choose $B>A>0$, $L=B-A$, a positive multiple $u=Lv$, and $a=Au+1$, $b=Bu+1$. Set

$$p=2ab-1,\qquad q=1+2B^2va.$$

Then $q-1=2B^2va$ and $q+1=2b(ABv+1)$. Multiplication shows $p+1=2ab\mid q^2-1$. The construction gives a search for examples by testing $p,q$ for primality. The following witness establishes existence at full size. An infinitude of prime pairs of this form is open here.

Take $A=1047655942105215289$, $B=2^{62}$, $u=(A+B)(B-A)\cdot83023756\cdot2^{300}$. Each prime has 1,024 bits and $q/p\approx1.294$. At $p+1$ the residual orders $(p+1)/\gcd(p+1,N-1)$ and $(p+1)/\gcd(p+1,N+1)$ have 511 and 513 bits. At the combined degree the residual order is one. At $q-1$ and $q+1$ the residual orders still have 124 and 509 bits. The first public label to expose a factor in the scan from 3 is 15. A separate Lean certificate checks the product and both primality claims.

| Operation on each label from 3 through 15 | Proper factors found | Work |
| --- | --- | --- |
| $\gcd(D_{N^2-1}(x)-2,N)$ | $p$ at 15 | 13 gcds, 53,222 ladder steps |
| $\gcd(D_{N-1}(x)-2,N)$ | None | 13 gcds, 26,611 ladder steps |
| $\gcd(D_{N+1}(x)-2,N)$ | None | 13 gcds, 26,611 ladder steps |
| $\gcd(x^{N^2-1}-1,N)$ | None | 13 gcds, 13 modular powers |

We also kept $p$ and replaced $q$ with the first prime in the earlier `predecessor-square-2048` fixture giving a 2,048-bit product. With the same degree formula and the same thirteen labels, all 53,222 ladder steps completed without a split. The replacement partner breaks the divisibility of $q^2-1$ by $p+1$. [Source of the control prime](../benchmarks/predecessor-square.json)

The expected factors are stored as decimal strings. The search sees only the product, choice of exponent, starting label and budget. The polynomial identities, the family divisibility and the probability inequality are proved in Lean. The cyclic-group counts and the population estimate below are paper arguments with finite numerical checks. [Fixture](../benchmarks/line-powers.json) · [Tests](../tests/test_line_powers.py)

## How often do two labels collide?

For a uniform independent pair of labels at one prime $r$, let $m_-=r-1$, $m_+=r+1$, $g_i=\gcd(d,m_i)$, $k_i=m_i/g_i$, $h_i=\gcd(2,k_i)$ and $h_0=\gcd(2,k_-,k_+)$. The exact probability is

$$C_r(d)=\frac{g_-^2(2k_--h_-)+g_+^2(2k_+-h_+)+2g_-g_+h_0}{4r^2}.$$

Within one group, the image of powering has size $k_i$, and each image element has $g_i$ preimages. Equal traces mean the powered elements are equal or inverse. This gives $2k_i-h_i$ ordered matches, since $h_i$ elements are their own inverses. Across groups only the common self-inverse image elements can match. These supply $h_0$ matches in each direction. A collision exposes exactly one prime with probability $C_p+C_q-2C_pC_q$. Related value-set and fiber-size formulas appear in the finite-field literature. The tests compare these two probabilities against direct counting for every odd prime up to 71 and every degree from 1 through 50. [Chou, Gomez-Calderon and Mullen](https://www.sciencedirect.com/science/article/pii/0022314X88900066) · [Brazelton, Harrington, Litman and Wong](https://tbrazel.github.io/assets/papers/dickson.pdf)

## A finite bound at 2,048 bits

Choose two distinct primes uniformly from $[X,2X)$ for $X=2^{1023}$, conditioned on their product having 2,048 bits. Given $N$, draw up to $2^{40}$ independent uniform labels modulo $N$. Compare any two of them after applying the same positive degree $e\mid N^2-1$, or compare a powered label with 2. **Even if every such degree is tried, the probability of a proper split by these comparisons is below $2^{-710}$.** This averages over both the prime pair and labels. It leaves open deterministic label choices that use additional information about the input, unequal degrees on the two sides, and other polynomial maps.

Put $d=N^2-1$. Composition gives $D_{ab}=D_a\circ D_b$, and $D_a(2)=2$. Any equality at a prime for degree $e$ therefore persists there at degree $d$. A proper gcd at $e$ may become the whole product at $d$, so the upper bound counts every equality at either prime. In the collision formula the net correction $-g_-^2h_--g_+^2h_++2g_-g_+h_0$ is nonpositive since $h_i\ge h_0$. Both $C_r$ and $H_r$ are thus at most $(g_-+g_+)/r$.

Fix $p$ and $M=p\pm1\le2X$. Since $p^2\equiv1\pmod M$, the local gcd is $\gcd(M,q^2-1)$. For an integer $a$, the number $\rho(a)$ of roots of 1 modulo $a$ is at most $2^{1+\omega(a)}$, by prime-power factorization, including the factor at 2. Summing even over composite partners $q$ gives

$$\sum_{X\le q<2X}\gcd(M,q^2-1)
 \le\sum_{a\mid M}\varphi(a)\rho(a)(X/a+1)
 \le6X\sum_{a\mid M}2^{\omega(a)}=6X\tau(M^2).$$

The last equality follows prime by prime, with contribution $2v+1$ when $\ell^v\Vert M$. To bound $\tau(M^2)^6/M$, take the product over primes $\ell<729$ of $\max_{0\le v\le9}(2v+1)^6/\ell^v$. For larger primes the maximum is 1, and for $v\ge9$ the consecutive ratio is at most $(21/19)^6/2\le1$. The exact rational product is smaller than $2^{247}$. Since $M\le2^{1024}$, this proves $\tau(M^2)<2^{212}$. [Exact rational check](../tests/test_line_powers.py)

There are fewer than $1.511X/\log X$ choices of $p$, and more than $(0.22X/\log X)^2$ eligible ordered prime pairs. Summing over the two signs and two prime positions bounds the average of $(g_-+g_+)/r$ summed at both primes by $24(1.511)(\log X)2^{212}/(0.22^2 X)<2^{-791}$. There are fewer than $2^{80}$ pair and neutral comparisons together at the maximal degree. A union bound proves the claim. This gives a reason to test other public degrees or study the structure of the labels before scaling the same experiment. [Prime-count constants and sources](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)
