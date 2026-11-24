# Searching all square-root classes at one coefficient

A single quadratic test found the two 1,024-bit primes of a constructed 2,048-bit product. The test covered all 2,199,023,255,552 square-root classes at one public coefficient. Replacing one prime gave another product with exactly as many classes. On that product the search proved the entire interval empty before trying a quadratic. For uniformly chosen primes of this size, the chance that this fixed search finds a factor is below $2^{-853}$. [Public inputs, work counts and expected results](../benchmarks/polynomial-packets.json) · [Decoder](../experiments/polynomial_packet.py)

## Where to look

Given $N$, choose a positive integer $A$ and a height cap $H$. A quadratic-sieve polynomial has the form $Q_B(x)=((Ax+B)^2-N)/A$ with $B^2\equiv N\pmod A$. Searching every root class $B\bmod A$ and every integer $x$ for $|Q_B(x)|\le H$ amounts to finding every nonnegative integer $m$ in
$$
L=\left\lceil\sqrt{\max(0,N-AH)}\right\rceil\le m\le
U=\left\lfloor\sqrt{N+AH}\right\rfloor,\qquad m^2\equiv N\pmod A.
$$
Both signs of $m=Ax+B$ give the same value. Each nonnegative $m$ gives its class directly as $B=m\bmod A$. The interval and equation use only the public inputs. A square $m^2-N=v^2$ gives a split if $\gcd(m-v,N)$ is a proper divisor. Other rows might help a separate smooth-relation search. [Height bounds for a single polynomial](polynomial-height.md) · [Earlier enumeration of square-root classes](crt-square-norms.md)

Set $c=\lfloor(L+U)/2\rfloor$ and $R=U-c$, assuming $L\le U$. An empty interval can be returned immediately. For $R>0$, continued fractions find $1\le k\le4R$ and a signed residue $b\equiv 2kc\pmod A$ with $|b|(4R+1)\le A$. Take $z$ to be the least nonnegative residue of $k(c^2-N)\bmod A$. Every root $m=c+t$ in the interval satisfies
$$
kt^2+bt+z=jA,\qquad |jA-z|\le E=kR^2+|b|R.
$$
If $16R^3\le A$, then $kR^2\le A/4$ and $|b|R<A/4$. Thus the closed interval $[z-E,z+E]$ contains at most one multiple of $A$. One integer square root of its discriminant gives at most two candidates. Integer division and the original congruence check each one. Checking the original congruence also handles $\gcd(k,A)>1$. A radius of zero needs just the test at the center. The computation uses $O(\log A)$ Euclidean divisions and a constant number of operations on integers of $O(\log(N+AH)+\log A)$ bits. Wider intervals can contain several multiples. The program reports their number and the number tested under the supplied budget. The earlier decoder used $m^2\equiv1\pmod N$ and needed a separate reading to locate the interval. Here the small norm itself supplies the endpoints. [Earlier interval search](short-root-interval.md) · [Euclidean and bounded-slope proofs](../PrimeFactors/RootIntervalSlope.lean) · [Scaled equation and explicit width proof](../PrimeFactors/PolynomialRootPacking.lean)

There is also a stronger asymptotic search. The monic quadratic $f(t)=(c+t)^2-N$ modulo the *known* modulus $A$ has exactly the desired translated roots in this interval. For every fixed $0<\epsilon<1/2$, Coppersmith's univariate theorem recovers all roots of size at most $A^{1/2-\epsilon}$ in time polynomial in $\log A$, after coefficient reduction. Input preparation also costs arithmetic in the size of $N$. This wider guarantee uses lattice reduction. The two measurements below use only the explicit continued-fraction calculation, and give no timing for the wider search. [Coppersmith, *Small solutions to polynomial equations*](https://research.ibm.com/publications/small-solutions-to-polynomial-equations-and-low-exponent-rsa-vulnerabilities)

## A finite bound on the number of candidates

For $k$ distinct integer roots $m_0<\cdots<m_{k-1}$ in an interval of span $D$, the Vandermonde determinant is positive. Let $e=\sum_{j=0}^{k-1}\lfloor j/2\rfloor=\lfloor(k-1)^2/4\rfloor$ for $k\ge1$. Then
$$
A^e\ \mid\ \prod_{i<j}(m_j-m_i),\qquad
A^e\le D^{k(k-1)/2}.
$$
Replace the monomial in column $j$ of the evaluation matrix by the monic degree-$j$ polynomial $(X^2-N)^{\lfloor j/2\rfloor}X^{j\bmod2}$. This preserves the determinant. Every entry in that column is divisible by $A^{\lfloor j/2\rfloor}$, giving the asserted divisor. This works with repeated prime factors in $A$ and with nonunit roots. For example, for $N\ge2^{2047},\ 2^{1000}\le A\le2^{1001}$ and $H=2^{420}$ the interval has span $D<2^{400}$ by rationalizing its endpoint difference. Five roots would force $2^{4000}\le A^4\le D^{10}<2^{4000}$. Thus across the entire family there are at most four nonnegative locations at that cap, regardless of any local root count. [Lean divisibility theorem](../PrimeFactors/PolynomialRootPacking.lean)

## A constructed success and a crossed comparison

Let $P$ be the product of the 39 odd primes through 173. Both runs use the same public $G=2^{260}P$, the 972-bit coefficient $A=G^2$, the cap $H=2^{308}$ and a budget of one candidate quadratic. The decoder receives only $N$ and those settings. A split at these settings requires the hidden half-gap to be a multiple of $G$ with quotient at most $2^{154}$. The successful product was deliberately chosen to meet those requirements.

| 2,048-bit product | Euclidean updates | Candidate quadratics | Rows under the cap | Factor search |
|---|---:|---:|---:|---|
| Planted half-gap | 144 | 1 | 1 | Two certified 1,024-bit primes |
| One prime replaced | 154 | 0 | 0 | Full cofactor unresolved |

The table counts completed Euclidean updates. The implementation can also perform a terminal denominator-budget comparison and division. Both radii have 255 bits, well within the explicit cube-root guarantee. For the planted product the one reduced value $Q$ is a 305-bit square. An ordinary Fermat search scanning consecutive midpoints from the next square would need more than $2^{250}$ tests. Each of the 39 odd primes contributes two roots modulo its square since $N$ is a nonzero square modulo that prime. The power of two contributes four because $N\equiv1\pmod8$. CRT therefore gives $4\cdot2^{39}=2^{41}$ classes in both examples. Neither a list of those classes nor their local roots is needed by the decoder. [Reproducible test](../tests/test_polynomial_packet.py) · [Fixture and complete decimal factors](../benchmarks/polynomial-packets.json)

To reproduce the construction, put $s=2^{152}+128905$. The planted pair has $q=p+2Gs$. Take the least $p_0\ge3\cdot2^{1022}$ satisfying $p_0\equiv1\pmod{2^{260}3^{165}}$ and $p_0+2Gs\equiv1\pmod{2^{260}5^{114}}$. Then $p=p_0+38780\cdot2^{260}3^{165}5^{114}$. For the crossed example, let $D=\operatorname{lcm}(G,2^{260}5^{114})$ and $q_0$ be the least integer at least $7\cdot2^{1021}$ congruent to $q\pmod D$. The replacement prime is $q'=q_0+73D$. We chose the large known divisors of the predecessors of these primes to make primality certificates inexpensive. These progressions themselves give factor information to anyone reading the construction. They are excluded from the search interface, as are $p,q,s$ and the candidate indices. The benchmark sends only the factor returned by discovery to the Lean certificate generator. The crossed pair's product and the primality of its two construction labels were also checked separately. [Certificate checker](../scripts/factor.py)

## How often could this work on an arbitrary product?

Draw two 1,024-bit primes independently and uniformly and condition on distinct primes with a 2,048-bit product. Set $X=2^{1023}$. There are more than $(0.22X/\log X)^2$ eligible ordered pairs, fewer than $1.511X/\log X$ choices for the first prime, and $\log X<710$. These explicit prime-count estimates apply without RH. [Derivation of prime counts](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)

For the fixed $A,H$ above, $AH<X^2$ and $N<4X^2$, so $0\le m<3X$. Every row determines a candidate product $N=m^2-AQ$ with $-H\le Q\le H$. Each such integer contributes at most two ordered pairs of distinct primes. The chance that there is *any* row under this cap is therefore bounded by $6X(2H+1)/(0.22X/\log X)^2<2^{-688}$.

For a direct split, a positive square $m^2-N=G^2s^2$ forces the prime pair to be $m-Gs, m+Gs$. For each first prime there are at most $2\lfloor\sqrt H\rfloor$ choices of partner, counting both signs of the difference. Multiplying by the upper bound on choices of first prime and dividing by the pair population gives a chance below $2^{-853}$. These bounds concern this particular fixed coefficient and cap. They leave open the research question of how to choose coefficients after seeing $N$, or how to combine larger rows efficiently. The counts are paper arguments. Lean checks the final numerical comparisons. [Checked constants](../PrimeFactors/PolynomialRootPacking.lean) · [Counting for adaptive coefficient choices](crt-screen-population.md)
