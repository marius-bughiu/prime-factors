# Relations among three or more Fermat discriminants

Given $N$, set $D(a)=a^2-N$ for integer midpoints $a\ge\sqrt N$. If a list of these values has product $r^2$, then $P=\prod a$ satisfies $P^2\equiv r^2\pmod N$. The quadratic sieve combines relations of this kind and tries a gcd to extract a divisor. We asked whether choosing the midpoints near $\sqrt N$ could guarantee that the gcd succeeds, or guarantee a relation small enough to find in that window. [Pomerance, *The Quadratic Sieve Factoring Algorithm*](https://math.dartmouth.edu/~carlp/PDF/paper52.pdf) · [Lean proofs](../PrimeFactors/ManyDiscriminants.lean)

## A window where a triple must yield a factor

Write $x=P\bmod N$. If $r<x$ and $x+r<N$, then $N\mid(x-r)(x+r)$ and both factors are strictly between 0 and $N$. Consequently $1<\gcd(N,x-r)<N$. The following sufficient condition can be checked **once for an entire window**, using only $N$.

Start at $m=\lceil\sqrt N\rceil$, put $d=m^2-N$, and take offsets between 0 and $K$ inclusive. Define
$$
L=d+2mK+K^2,\qquad R=\lceil\sqrt{L^3}\rceil,\qquad E=3dK+3mK^2+K^3.
$$
Compute $t=\lfloor md/N\rfloor$. If
$$
tN+R<md,\qquad md+E+R<(t+1)N,
$$
then *every* square-product triple from this window yields a proper gcd. Indeed each discriminant is at most $L$, so its triple's square root is at most $R$. For three offsets $i,j,k$, expansion of the midpoint product gives
$$
P\equiv md+d(i+j+k)+m(ij+ik+jk)+ijk\pmod N.
$$
The three offset-dependent terms have sum between 0 and $E$. The two inequalities put the reduced residue strictly between $r$ and $N-r$. Lean verifies this implication, including the endpoints. The check uses a constant number of operations on integers with $O(\log N)$ bits for $K\le\sqrt N$. Locating a square product among $K+1$ distinct positions by testing all triples still costs $\binom{K+1}{3}$ square tests. [Window theorem](../PrimeFactors/ManyDiscriminants.lean)

At $N=723889$, the gate passes with $m=851$, $d=312$, $K=2$, $t=0$, $R=226890$ and $E=12092$. The first three midpoints have discriminants $312,2015,3720$, whose product is $48360^2$. One gcd gives 709, and the cofactor is 1021. Ordinary Fermat search first succeeds at midpoint 865. Lean checks the gate, the prime factors and the product. [Checked example](../PrimeFactors/ManyDiscriminants.lean)

## Why a square relation can still fail

Even a relation whose proper subproducts are all nonsquares can give one of the two trivial congruences $P\equiv\pm r\pmod N$. Both examples below use parity-compatible midpoints in the balanced interval.

| $N$ | Midpoints | Discriminants | Square root $r$ | Result |
| --- | --- | --- | --- | --- |
| $20099=101\cdot199$ | $142,144,148$ | $65,637,1805$ | $8645$ | $P\equiv11454\equiv-r\pmod N$, and $\gcd(N,P-r)=1$. |
| $96673=277\cdot349$ | $315,317,319,323$ | $2552,3816,5088,7656$ | $19476864$ | $P\equiv45591\equiv r\pmod N$, and $\gcd(N,P+r)=1$. |

The module checks every individual nonsquare in both rows and all six nonsquare pairs in the second. A square triple inside the second row would force the remaining term to be a square because the entire product is square. Thus smaller dependencies do not account for these failures. [Checked counterexamples](../PrimeFactors/ManyDiscriminants.lean)

There is a direct way to recognize some such relations before testing their gcd. If $N=m^2-ij$ with $i,j>0$, write $d=ij$ and $T=2m+i+j$. Then $D(m)=d$, $D(m+i)=iT$, $D(m+j)=jT$, and $(m+i)(m+j)=mT-N$. The resulting triple has $r=dT\equiv P\pmod N$. For instance, take $i=3,j=4$ and $m\equiv17\bmod30$. The three discriminants are nonsquares since $d=12$, $3T\equiv3\bmod5$ and $4T\equiv2\bmod3$. Also $N$ is odd, $\gcd(N,12)=1$, and $(2m+7)(2m-7)=4N-1$ implies $\gcd(N,T)=1$. Neither gcd gives a proper factor. For all sufficiently large $m$ in this progression the three positions are in the first five midpoints above $\sqrt N$. This is an infinite family of integer inputs.

If also $d=uv$ then, by the same identity applied twice, the four displaced midpoints have square-product root $d(2m+i+j)(2m+u+v)\equiv P\bmod N$. This explains the second row with $m=311$ and $d=48=4\cdot12=6\cdot8$. These symbolic constructions are algebraic deductions on paper.

## How many inputs admit a small square product?

**Paper bound.** For each $\delta>0$, at most $O_\delta(R^{1+\delta})$ positive integers $N$ admit a relation with $1\le r\le R$ containing at least two distinct positive Fermat discriminants. This allows lists of any length and midpoints arbitrarily far above the square root.

Fix $r$ and choose any two distinct discriminants $d=a^2-N<e=c^2-N$ from the relation. Both divide $r^2$. Their difference satisfies $e-d=(c-a)(c+a)$. Once we choose a divisor $k=c-a$ of $e-d$, we recover
$$
a=\frac{(e-d)/k-k}{2},\qquad N=a^2-d.
$$
Thus the number of possible inputs for this $r$ is at most
$$
\tau(r^2)^2\max_{1\le j\le r^2}\tau(j),
$$
where $\tau$ counts positive divisors. The finite enumeration and its cardinality bound are proved in Lean. To see the paper asymptotic, for any $\eta>0$, $\tau(s)\ll_\eta s^\eta$. In the prime factorization of $s$, each prime $p\ge2^{1/\eta}$ satisfies $e+1\le 2^e\le p^{\eta e}$. The finitely many smaller primes contribute bounded factors $\sup_{e\ge0}(e+1)/p^{\eta e}$. Taking $\eta=\delta/6$ and summing over $r\le R$ proves the stated bound. [Lean enumeration](../PrimeFactors/ManyDiscriminants.lean)

Choose distinct primes $X\le p<q\le2X$ and put $N=pq$. There are $\asymp X^2/(\log X)^2$ such inputs by the prime number theorem. For any fixed $0<\varepsilon<1$, the fraction admitting any such relation with $r\le N^{1-\varepsilon}$ tends to zero. Apply the bound with $R=(4X^2)^{1-\varepsilon}$ and choose $\delta$ with $(1-\varepsilon)(1+\delta)<1$. In particular, for $0<\varepsilon<1/6$, almost all these inputs have **no** square-product triple of distinct midpoints among the first $\lfloor N^{1/6-\varepsilon}\rfloor+1$ positions. Each discriminant there is $O(\sqrt N\,(1+N^{1/6-\varepsilon}))$, so the square root of a triple product is $O(N^{1-3\varepsilon/2})$, within the preceding bound for sufficiently large $N$. [Prime number theorem project](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)

The count uses the actual integer square root of the product of the unreduced discriminants. A large $r$ can have a small residue modulo $N$. The bound gives no corresponding restriction on that residue and no running-time lower bound for general quadratic-sieve searches.
