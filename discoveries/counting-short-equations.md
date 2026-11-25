# Counting short equations with a factorial bound

Seven coefficients suffice to check a wider interval around any chosen odd center. For an odd input $N\le 2^{2048}$ coprime to 45,360, at most six polynomial roots give all possible indices $x$ for divisors $d=c+2x\ge 2^{1023}$ in the interval. The guaranteed radius in $x$ grows from $13\cdot2^{435}$ to $267\cdot2^{431}$, about **28.4% wider**. For a 2,048-bit product with a cofactor of at most 1,024 bits, the public lower bound $d\ge\lceil N/2^{1024}\rceil$ gives radius $5\cdot2^{437}$, about **53.8% wider** than the earlier fixed-floor guarantee. These are existence results at a center we choose. Finding a winning center and constructing its short equation both require work. [Seven-row theorems](../PrimeFactors/SiftedDivisorWindow.lean) · [Previous construction and actual runs](sifting-a-divisor-window.md)

## Why counting more coefficient vectors helps

Suppose a vector of $r$ integers has one of $J$ possible labels, and moving coordinate $i$ by one costs a positive integer $w_i$. We want two distinct vectors with the same label and weighted distance strictly less than $M$. The earlier proof used a box that allocated an equal part of the distance budget to each coordinate. Counting all the positions available in a weighted ball gives the sufficient condition

$$
J\,r!\prod_i w_i < M^r.
$$

The former constant was $r^r$. In seven dimensions $7^7/7!=823543/5040\approx163.4$. This factor measures the additional room in the counting inequality. The product of the seven polynomial weights grows roughly as the **21st power** of the window radius, so the gain in radius is much smaller. The argument works for any assignment of the labels, including a nonlinear one. For additive labels, the difference of the two vectors has label zero. The strict inequality matters already in dimension one, where parity gives two labels and distinct equally labelled integers have distance at least two. [General theorem and strict endpoint example](../PrimeFactors/FactorialCollision.lean)

The geometric idea is classical. A ball of diameter $M$ in this weighted distance has volume $M^r/(r!\prod_i w_i)$. A translation with more than $J$ lattice points forces a collision. The Lean proof gives a finite version with an explicit integer mesh, which also works for arbitrary labels on the integer points. [Blichfeldt, 1914](https://doi.org/10.2307/1988585) · [Finite proof](../PrimeFactors/FactorialCollision.lean)

1. Choose $t=r^2M^{r-1}+r+1$, let $Q=2t$, and put $S=tM-r-1$. Count all nonnegative $r$-tuples $c$ whose sum is at most $S$. Introducing a slack coordinate gives $\binom{S+r}{r}$ choices. Independently choose a sign for each coordinate. Encode it as $z_i=c_i$ or $z_i=-c_i-1$, giving $2^r\binom{S+r}{r}$ distinct points with $\sum|z_i|\le S+r<tM$.
2. Record the remainders $z_i\bmod(Qw_i)$ and the original label of the vector $u_i=\lfloor z_i/(Qw_i)\rfloor$. These records have at most $JQ^r\prod_i w_i$ values. Write $A=Jr!\prod_i w_i$. The strict integer hypothesis gives $A+1\le M^r$. The inequality $a^r-b^r\le r(a-b)a^{r-1}$ for $a\ge b\ge0$ then gives $A t^r<(S+1)^r$. Finally $(S+1)^r\le r!\binom{S+r}{r}$, so the signed points outnumber the records.
3. Two points with the same record have the same remainder in every coordinate. For their coarse vectors $u,v$, the difference at coordinate $i$ satisfies $Qw_i(u_i-v_i)=z_i-z'_i$. Their weighted distance is strictly less than $M$ by the triangle inequality. Distinct fine points with identical remainders also give distinct coarse vectors.

## Applying the count to seven rows

The label records three Taylor coefficients of the cleared polynomial, modulo $N^3,N^2,N$. There are at most $N^6$ labels. A short difference of two coefficient vectors gives an equation vanishing at every divisor in the chosen interval, because its cleared value has the required divisibility by $d^3$ and the underlying integer value is strictly smaller in magnitude. The existing interpolation basis leaves degree at most six. The same general argument gives a factorial bound for ordinary binomial coordinates of any degree. [Sifted equations and divisibility](../PrimeFactors/SiftedDivisorWindow.lean) · [General binomial-row theorem](../PrimeFactors/FactorialCollision.lean)

For the seven-row parameters put $D_i=(1,1,6,6,360,360,45360)_i$ and $P(R)=\prod_{i=0}^6\max(1,\lfloor (R+74)^i/D_i\rfloor)$. The 74 covers the full range of public shifts and interpolation nodes. Two strict integer comparisons establish the quoted bounds.

| Divisor floor | Radius in parity indices $R$ | Sufficient comparison |
|---|---:|---|
| $2^{1023}$ with $N\le2^{2048}$ | $267\cdot2^{431}$ | $7!P(R)<2^{9195}$ |
| $D=\lceil N/2^{1024}\rceil$ with $N\ge2^{2047}$ | $5\cdot2^{437}$ | $7!P(R)<2^{9201}$ |

For the second comparison, $N\le 2^{1024}D$ and $D\ge2^{1023}$. Thus $N^6 7!P(R)<2^{6\cdot1024+9201}D^6\le D^{21}$. For reference, at $R=2^{439}$ the old constant gives $7^7P(R)>2^{9201}$ by about 0.029 binary digits, while the factorial constant passes with about 7.324 digits to spare. This comparison concerns these explicit sufficient bounds. It gives no lower bound on the radius attainable by a particular polynomial. The interval for candidate divisors is $[c-2R,c+2R]$, including both ends and testing only odd candidates. [Kernel-checked budgets](../PrimeFactors/SiftedDivisorWindow.lean) · [Public divisor floor](../PrimeFactors/CoupledDivisorWindow.lean)

The two comparisons can also be reproduced with exact integer arithmetic.

```python
from math import factorial, prod

def weights(radius):
    denominators = (1, 1, 6, 6, 360, 360, 45360)
    return prod(max(1, (radius+74)**i // d) for i, d in enumerate(denominators))

assert factorial(7)*weights(267*2**431) < 2**9195
assert factorial(7)*weights(5*2**437) < 2**9201
assert factorial(7)*weights(2**439) < 2**9201 <= 7**7*weights(2**439)
```

The finite mesh proves existence and could be enumerated if label equality is decidable. For an additive label one could instead enumerate every integer row of weighted norm below $M=D^3$, testing the congruences directly. Both are much larger calculations than a seven-row lattice reduction. The proof gives no guarantee that a particular reduction returns a qualifying row at the wider radius. The earlier measured successes and misses at selected centers retain their original radii. [Measured search costs](sifting-a-divisor-window.md)

## Choosing the seven-row window from boundary readings

Suppose the distinct primes satisfy $p<q\le2p$, $q<2^{1024}$, $N=pq\ge2^{2047}$, and $\gcd(N,45360)=1$. Up to **1,168 boundary readings** in two batches select one seven-row equation with at most six possible integer offsets for the larger factor. Each reading of the dephased principal Dirichlet $L$-function ratio $B(t)$ needs absolute error at most $1/8$. The integer heights can reach $2^{584}$. The preceding conditional result used up to 1,000 readings through $2^{500}$ and a 24,576-row equation. Seven-row equations have run on the project's test inputs. No full-size factor has been recovered by obtaining these readings from the input. The cost of computing them with certified error at the specified heights remains open. [Conditional seven-row theorem](../PrimeFactors/SevenRowBoundaryWindow.lean) · [Definition of the readings and two-batch protocol](two-batches-of-boundary-readings.md)

The readings give a lower endpoint $a$ for $(\log q-\log p)/2$ with uncertainty at most $\pi/(3\cdot2^{583})$. Thus $X=\sqrt N e^a\le q$ and $q-X\le (\pi/3)2^{441}$. The seven-row radius $R=5\cdot2^{437}$ gives a physical span $4R=(5/4)2^{441}$. Lean checks $q-X+1\le4R$, so rounding $X$ down to $L=\lfloor X\rfloor$ preserves coverage. At the odd center $C=2\lfloor L/2\rfloor+1+2R$ the polynomial has a root $x$ with $|x|\le R$ and $q=C+2x$. Both the prescribed center and its equation are independent of the unknown factor values. [Rounding and factor coverage](../PrimeFactors/SevenRowBoundaryWindow.lean)
