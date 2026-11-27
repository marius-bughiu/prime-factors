# A zeta coefficient that determines both factors

For a product $N=pq$ of two distinct primes, one Dirichlet coefficient determines the factors exactly. It is the coefficient at $N$ of $\zeta''(s)/\zeta(s)$. For any positive multiplier, remove whole copies of $N$ from it and take one ordinary gcd with $N$. This either finds a factor directly or tells us that the requested coefficient is zero or an exact copy of the original. A fast way to compute the original coefficient from $N$ remains open. [Lean proofs](../PrimeFactors/SelbergMultipleCoefficients.lean)

## The exact reading

Write $C(n)$ for the second generalized von Mangoldt function. It is the Möbius transform of the squared logarithm. Selberg's convolution identity gives

$$
C(n)=\Lambda(n)\log n+\sum_{de=n}\Lambda(d)\Lambda(e).
$$

Here $\Lambda(p^a)=\log p$ for $a\ge1$ and $\Lambda$ vanishes elsewhere. For $p^a q^b$ with distinct primes and both exponents positive, the only contributing ordered pairs are $(p^a,q^b)$ and $(q^b,p^a)$. Thus $C(p^a q^b)=2\log p\log q$ at every such pair of powers. On any integer with three distinct prime divisors the coefficient vanishes. Lean proves the convolution identity from Mathlib's von Mangoldt function and proves both evaluations. These classical coefficient identities have a Dirichlet-series interpretation in the half plane $\Re(s)>1$. [Selberg's original paper](https://www.math.lsu.edu/~mahlburg/teaching/handouts/2014-7230/Selberg-ElemPNT1949.pdf) · [Banks and Sinha, equations (1.4) and (1.5)](https://arxiv.org/pdf/2209.11768#page=3)

For $p<q$, put $L=\log N$. The public product gives $L=\log p+\log q$, so

$$
L^2-2C(N)=(\log q-\log p)^2,\qquad
p=\exp\!\left(\frac{L-\sqrt{L^2-2C(N)}}2\right).
$$

The output follows from an **exact** supplied value of $C(N)$. Directly summing over divisor pairs already encounters the factors. [Kernel-checked recovery formula](../PrimeFactors/SelbergMultipleCoefficients.lean)

## What a different multiple can tell us

For any positive integer $k$, divide out whole copies of $N$ to obtain $k=N^j u$ with $N\nmid u$. Calculate $g=\gcd(u,N)$.

| Public observation | Consequence |
| --- | --- |
| $u=1$ | $kN=N^{j+1}$ and $C(kN)=C(N)$. |
| $u>1$ and $g=1$ | A prime dividing $u$ supplies a third prime divisor, so $C(kN)=0$. |
| $g>1$ | $g<N$ because $N\nmid u$. The gcd is a proper factor of $N$. |

This holds for every positive multiplier, including one chosen after observing earlier coefficients. A procedure can simulate each exact answer from a single value $C(N)$ until the public gcd has already factored $N$. The arithmetic costs at most $\lfloor\log_N k\rfloor$ successful divisions, one final divisibility check and one gcd on integers of the supplied sizes. Constructing or reading $k$ has its own cost. For $1<k<p$ every reading is zero. [Lean multiplier trichotomy](../PrimeFactors/SelbergMultipleCoefficients.lean)

For example, $N=18{,}079$ gives $C(N)=47.88082132261359669\ldots$. The formula recovers $101$ and then $N/101=179$. We independently evaluated the convolution by trying every integer $d$ from 1 through $\lfloor\sqrt{kN}\rfloor$, checking divisibility, testing the two entries for prime-power support, and counting both orientations for unequal entries.

| $k$ | $u$ | $g$ | $C(kN)$ | Divisor positions tried |
| ---: | ---: | ---: | --- | ---: |
| 1 | 1 | 1 | $C(N)$ | 134 |
| 2 | 2 | 1 | 0 | 190 |
| 18,079 | 1 | 1 | $C(N)$ | 18,079 |
| 101 | 101 | 101 | $C(N)$ | 1,351 |
| 202 | 202 | 101 | 0 | 1,911 |

The last two rows show why the proper-gcd branch can stop before predicting the coefficient. The gcd gives the same prime in both cases, although the coefficients differ.

## Precision at 2,048 bits

A candidate smaller factor $x$ predicts $F_N(x)=2\log x\,(\log N-\log x)$. For $0<x\le y$, $y^2\le N\le2x^2$, Lean proves

$$
0\le F_N(y)-F_N(x)\le\frac{2(y-x)}{x}.
$$

The exact difference factors as $2\log(y/x)\log(N/(xy))$. The first logarithm is at most $(y-x)/x$ and the second lies between zero and one. With $x\ge2^{1023}$, the predictions for two adjacent odd positions $x,x+2$ satisfying these inequalities differ by at most $2^{-1021}$. Error intervals of radius $2^{-1022}$ around those two predictions overlap. A reading inside that overlap cannot eliminate either position using this real-valued constraint alone. An independent divisibility test can eliminate a false candidate. This limits this use of a noisy coefficient, and gives no lower bound for other factoring algorithms. [Lean spacing and full-size bound](../PrimeFactors/SelbergMultipleCoefficients.lean)

Banks and Sinha's Theorem 1.3, under RH, estimates a twisted **sum** of these coefficients through $X$. At order two its stated error is $O(\sqrt X\log^5(X+|t|))$. Subtracting the estimates at $N$ and $N-1$ gives two remainder terms of that scale, even at $t=0$. This estimate alone cannot certify an individual reading at the precision above. Correlated errors or a different pointwise evaluator would require a separate argument. The exact recovery, trichotomy and spacing bounds here are unconditional. [Banks and Sinha, Theorem 1.3](https://arxiv.org/pdf/2209.11768#page=4) · [Pinned RH statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)
