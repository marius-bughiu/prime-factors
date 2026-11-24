# Near-square totients with unbounded squarefree part

There are infinitely many balanced prime pairs $p<q<2p$ for which the product alone recovers the factors in at most **49 discriminant tests**, even though the squarefree part of $\varphi(pq)$ exceeds any prescribed bound. Here the squarefree part $\operatorname{sf}(a)$ is the unique squarefree $d$ with $a=d y^2$. More precisely, one fixed $k\in\{1,\ldots,49\}$ occurs along a sequence with unbounded squarefree part, $q/p$ tending to a constant strictly between 1 and 2, and
$$\varphi(N)=(\lfloor\sqrt N\rfloor-1)^2-k^2.$$
For any fixed $L\ge1$, allowing these square errors alongside error zero in a search for $\varphi(N)=d y^2-e$ with $d\le L$ therefore strictly extends the inputs covered by exact bounded square classes. The infinitude argument is unconditional and uses a theorem on 50 admissible linear forms. [Exact square-class decoder](discriminant-strides.md) · [Kim, Lemma 2.1](https://www.csun.edu/~sungjin/SJK_Totient2-3%281%29.pdf#page=4)

## The product-only calculation

For $200\le j\le249$, set $P_j(t)=j^2t+2j+1$. Suppose $p=P_i(t)$ and $q=P_j(t)$ are prime, $i<j$ and $t\ge1$. Set $k=j-i$ and $Y=ijt+i+j$. Expanding gives
$$
(p-1)(q-1)=Y^2-k^2,\qquad
N=(Y+1)^2+k^2(t-1).
$$
The factor ratio is below two already at $t=1$ and for every larger $t$, since $P_j(t)\le250^2t<2\cdot200^2t<2P_i(t)$. Since $2ij>k^2$, the last term is smaller than $2Y+3$, so $s=\lfloor\sqrt N\rfloor=Y+1$. For each $1\le k\le49$ with $k^2\mid N-s^2$, try
$$S=N+1-(s-1)^2+k^2.$$
If $S^2-4N$ is a nonnegative square, use its root to reconstruct the two factors and verify their product. Only $N$ is supplied. For $N=20995182420991$, $s=4582050$ and $N-s^2=218491$. The surviving $k$ are 1, 7 and 49. The last gives $3680401\cdot5704591$. Here $i=200$, $j=249$, $t=92$ and $\operatorname{sf}(\varphi(N))=2\cdot5\cdot29\cdot79\cdot83\cdot3067=5831992510$.

A 92-bit example shows the filter working before the factors are known. For $N=2723154578512940020180564043$, $N-\lfloor\sqrt N\rfloor^2=1985348667707$. Through $k=43$ only 1 and 43 have squares dividing this residual. The second discriminant gives $42949673760401\cdot63403382146843$. The prime $130459634047$ divides the totient exactly once, so every exact square-class multiplier is at least that large. The certificate for the larger factor also proves this auxiliary prime is prime. With the index-gap cap set to 42, the same search leaves the full input unresolved. [Decimal benchmark and control](../benchmarks/square-offset.json) · [Lean identities, integer-root decoder and multiplier bound](../PrimeFactors/PredecessorCount.lean)

## Simultaneous primality and large squarefree part

Fix $L$. For each index $i$ choose a distinct prime $r_i$ larger than $L$, 249, and all $|i+2j(i-j)|$ for the 50 indices $i,j$. These integers are nonzero. When $j\le i$ they are positive, and when $j>i$ we have $2j(j-i)>i$. Require
$$it+2\equiv r_i\pmod {r_i^2}.$$
Then $r_i$ divides $P_i(t)-1=i(it+2)$ to exponent exactly one. For $j\ne i$, the residue of $i(P_j(t)-1)$ is $2j(i-j)\ne0\bmod r_i$. Every $P_j(t)$ is also a unit modulo $r_i$, since $iP_j(t)\equiv i+2j(i-j)\bmod r_i$. Thus if $P_i(t)$ and $P_j(t)$ are prime, their totient has both $r_i$ and $r_j$ in its squarefree part.

To handle the small primes, require $t$ even. At each odd prime $\ell\le50$ choose a quadratic nonresidue $\nu_\ell$ and impose $t\equiv1-\nu_\ell\bmod\ell$. The coefficient $t$ is nonzero, and the polynomial $t j^2+2j+1$ in the index $j$ has nonsquare discriminant $4\nu_\ell$. Thus all 50 forms are units at $\ell$. The Chinese remainder theorem combines these conditions and the private prime conditions into a single progression $t=t_0+Mu$ with $t_0>0$.

The resulting 50 forms in $u$ are admissible. At a prime dividing $M$ the preceding checks apply. At any other prime $\ell>50$, a form with $\ell\mid j$ is identically one, and each remaining form excludes just one residue of $u$. The 50 forms cannot cover all residues. Their leading coefficients are positive, and their pairwise determinants are nonzero because $(2j+1)/j^2$ is strictly decreasing and an affine substitution with slope $M>0$ preserves nonproportionality.

Kim's quantitative general-linear-forms theorem gives $\gg_L X/(\log X)^{50}$ positive parameters with at least two prime values and all values at most $X$, for sufficiently large $X$ depending on the fixed progression. Each specified pair of indices has strictly increasing product, so a product can be counted at most $\binom{50}{2}$ times. This yields the same order of lower bound for distinct products at fixed $L$. The implied constant depends on the progression for this $L$. [Kim, Lemma 2.1](https://www.csun.edu/~sungjin/SJK_Totient2-3%281%29.pdf#page=4)

As $L$ increases, the 1,225 possible index pairs stay fixed, and the squarefree parts are at least $r_i r_j>L$. At least one pair of indices must therefore have unbounded squarefree parts. Along such a sequence $t\to\infty$, $q/p\to(j/i)^2\in(1,2)$ and the error remains the single fixed square $(j-i)^2$. Pigeonholing gives existence of the recurring pair.

## Comparison with weighted Fermat

Ordinary Fermat search needs $\Theta(\sqrt N)$ midpoint increments along the recurring family, since $(p+q)/2-\sqrt N\sim(j-i)^2t/2$. The weighted Fermat method can also exploit the family. Indeed
$$j^2p-i^2q=(j-i)(2ij+i+j)$$
is constant at fixed $i,j$. Dividing its square by $j^2p+i^2q+2ij\sqrt N$ shows that $j^2p+i^2q=\lceil2ij\sqrt N\rceil$ for sufficiently large $t$. One weighted discriminant test then suffices for the correct weights, which can be included in a finite list independent of $N$. The separation proved here concerns bounded *exact totient square classes*. Establishing a speed advantage over weighted Fermat would require a different comparison. [Weighted Fermat windows](searching-the-balanced-interval.md) · [Lehman's factoring algorithm](https://doi.org/10.1090/S0025-5718-1974-0340163-2)

## Recovering an unknown direction with continued fractions

The finite list can be removed when the common parameter is large enough. Write $i=ga$, $j=gb$, where $g=\gcd(i,j)$, $a<b$, and put $d=b-a$. Assume $d^2\le2ab$ and $t>1$, so the same floor identity holds. With $s=\lfloor\sqrt N\rfloor$, $R=N-s^2$ and $C=(ga+1)(gb+1)$, the public ratio satisfies

$$R=g^2d^2(t-1),\qquad \frac{s}{R}=\frac{ab}{d^2}+\frac{C}{R}.$$

The fraction $ab/d^2$ is reduced because $a,b$ are coprime and each is coprime to $b-a$. If **$R>2C d^4$**, Legendre's continued-fraction criterion puts $ab/d^2$ among the ordinary convergents of $s/R$. Equivalently, $t-1>2(a+1/g)(b+1/g)d^2$. The decoder enumerates the convergents from the product. It does not need to know $a,b,g,t$ or the size of the totient error in advance. [Lean recovery theorem](../PrimeFactors/ContinuedSquare.lean)

For a candidate $u/v$, check $v\mid R$ and test whether $v$ and $4u+v$ are squares. At the genuine convergent their roots are $d$ and $a+b$, which give $a,b$. Now $C=s-u(R/v)$ and $C-1=ug^2+(a+b)g$. The quadratic formula recovers $g$ when its discriminant is a square and its positive root is integral. Verify $g^2 v\mid R$, reconstruct $t=1+R/(g^2v)$ and require $P_{ga}(t)P_{gb}(t)=N$ with two proper factors. Euclidean division produces $O(\log N)$ convergents. Each uses polynomial work in $\log N$. Every returned split has the displayed integer parametrization, including any hit found outside the sufficient approximation inequality. [Product-only implementation](../experiments/continued_square.py)

On $N=2133224365312947428491988216494183314257$ the eleventh convergent recovers $a=1009,b=1301,g=1,t=35184372093650$. Six integer square tests after the initial square root give $35820540725475287669\cdot59553103390084086253$. Its totient error is $292^2=85264$, its two prime predecessors have gcd 4, and consecutive Fermat search would take 1,499,980,151,096,486,799 increments. A ten-convergent cap leaves it unresolved.

The sixth structured 2048-bit fixture takes $a=13$, $b=15$, $t=10000$, $g=1372814\cdot2^{481}$ and primes $p=P_{13g}(10000)$, $q=P_{15g}(10000)$. The public ratio yields $195/4$ on the third convergent. Seven square tests after the initial square root and one direction test recover the factors. Their relative gap is 33.14% and the square correction $(2g)^2$ has 1005 bits. The 504-bit common divisor of the two prime predecessors facilitated their primality certificates. Weighted Fermat also applies at the reduced direction $13,15$. The earlier 2048-bit exact six-scale fixture exhausts all 615 convergents. [Decimal fixtures and results](../benchmarks/continued-square.json) · [Lean theorem](../PrimeFactors/ContinuedSquare.lean) · [Decoder](../experiments/continued_square.py)

```sh
python3 experiments/continued_square.py 2133224365312947428491988216494183314257
```

### Escaping every finite list of scales and errors

Fix positive $L$ and nonnegative $E$. The same construction supplies infinitely many distinct balanced prime pairs satisfying the convergent criterion and **none** of the relations $\varphi(N)=h y^2-e$ with $1\le h\le L$ and $|e|\le E$. Use the 50 indices $I_h=Gh+1$, $200\le h\le249$, for an integer $G>\sqrt E$. For every pair of actual indices $i<j$ the correction $k^2=(j-i)^2$ now exceeds $E$. All 50 linear forms retain the small-prime admissibility and the ratio bounds above. The private primes can again be chosen larger than every fixed index and every absolute value used in their congruences.

For each of the finitely many choices $(i,j,h,e)$, reserve a new prime $\ell>105$ coprime to $2hij(e-k^2)$ and to the prior modulus. Choose a residue of $t$ modulo $\ell$ for which $(Y(t)^2+e-k^2)/h$ is a quadratic nonresidue, and all 50 linear forms are nonzero. Such a residue exists. As $t$ varies, $Y(t)=ijt+i+j$ takes every residue. For $c=e-k^2\ne0\bmod\ell$, the equation $v^2-u^2=c$ has exactly $\ell-1$ solutions by choosing the nonzero first factor in $(v-u)(v+u)=c$. With $\chi$ the quadratic character extended by $\chi(0)=0$, it follows that $\sum_u\chi((u^2+c)/h)=-\chi(h)$. At most two arguments give zero. At least $(\ell-3)/2>50$ give nonresidues, and the 50 prime forms together exclude at most 50 residues. The additional CRT conditions therefore preserve admissibility. On the chosen progression they exclude every claimed scale and error for every possible prime pair.

Apply Kim's lemma to the resulting fixed forms. All sufficiently large parameters satisfy the continued-fraction inequality simultaneously for every pair, since there are finitely many directions and $a,b,g$ are fixed for this progression. For each fixed $L,E$ this again yields $\gg_{L,E} X/(\log X)^{50}$ distinct products with both primes at most $X$. Varying $L,E$ gives a sequence outside every fixed finite list. Along a subsequence the two labels $h$ are fixed and $q/p$ tends to their squared ratio. The identity $\gcd(I_h,I_l)\mid l-h$ follows because their gcd divides $G(l-h)$ and is coprime to $G$. Thus every reduced index gap $(I_l-I_h)/\gcd(I_h,I_l)$ is at least $G$.

This also gives a separation from any **preassigned finite list of weighted Fermat directions**. Choose $G$ large enough that none of the listed weight ratios equals the square of a reduced direction in the tuple, in either orientation. This is possible because the reduced numerator or denominator of every such squared ratio is at least $G^2$. For fixed $G$, each erroneous pair of weights $u,v>0$ gives $uP_i(t)-vP_j(t)=(ui^2-vj^2)t+O(1)$ with nonzero leading coefficient. Its weighted sum lies $\Theta(t)$ above $2\sqrt{uvN}$, so even a fixed power of $\log N$ consecutive weighted midpoint tests misses for all sufficiently large $t$. The growing-weight continued-fraction search succeeds on the constructed prime pairs. This argument concerns finite lists fixed before the input. It leaves open cost comparisons with adaptive or expanding weighted searches. [Quantitative prime-tuple theorem](https://www.csun.edu/~sungjin/SJK_Totient2-3%281%29.pdf#page=4)

### How many inputs can this model cover?

Even without the approximation inequality, every integer pair from the model with both factors at most $2X$ has $t<2X$ and each index at most $\sqrt{2X/t}$. Summing $2X/t$ over positive $t<2X$ bounds the total number of such pairs by $O(X\log(2X))$, uniformly over **all** indices and scales. For two primes sampled uniformly without replacement from $[X,2X)$ the fraction covered is consequently $O((\log X)^3/X)$ by the prime number theorem. Globally up to $X$, the family of guaranteed prime successes has cardinality $X^{1+o(1)}$ by combining the upper bound and the fixed-progression lower bound. This exponent measures cumulative coverage. The lower bound carries no uniformity as $L,E$ grow.

For exactly 2048-bit products of uniform distinct 1024-bit primes, the same count gives a finite limit on **every possible success of this decoder**. Set $X=2^{1023}$. Even including composites, at most $2X(1+\log(2X))$ candidate pairs fit in the full box by the harmonic-sum bound. The conditioned population has at least $(0.22X/\log X)^2/2$ prime pairs. Since $\log(2X)<710$, division gives a probability less than $[4\cdot711\cdot710^2/0.22^2]/X<2^{-988}$. The constructed examples exercise a provably sparse relation at the target size. [Lean count for each parameter](../PrimeFactors/PredecessorCount.lean) · [Finite prime-pair denominator](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)
