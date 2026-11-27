# Can an average pick out the factor sum of one number?

Can an average recover $17+31$ from their product, 527? The index of a modular group at level 527 encodes that sum exactly. A proposed way to read that index is to average a known function while tuning the average to 527. But 528 contributes to the same reading. Even after subtracting all contributions from divisors up to 7, the interference from 528 alone exceeds the precision needed for rounding at every frequency height up to 527. [Lean proof, including the example](../PrimeFactors/IndexCoefficientWindow.lean)

## What the reading measures

For any positive integer $m$, the normalized index is $a(m)=\sum_{d\mid m,\ d\ {\rm squarefree}}1/d$. For $N=pq$ with distinct primes, $N a(N)=(p+1)(q+1)$. An exact reading gives the factor sum by subtracting $N+1$. Csirik, Wetherell and Zieve give the Dirichlet series for $a(m)$ and use it to compute an average over all levels. [Original paper, §§2 and 5](https://arxiv.org/pdf/math/0006096#page=5)

Grant the reader exact subtraction of every squarefree divisor term with $d\le Y$. Let $b_Y(m)$ be the remaining sum. If $1\le Y<p<q$, then $b_Y(N)=(p+q+1)/N$. Let $F_Y(s)=\sum_{m\ge1}b_Y(m)m^{-s}$. The reading considered here averages $N^{2+it}F_Y(2+it)$ for $-T\le t\le T$, weighting frequencies by the triangle $(1-|t|/T)/T$ for $T>0$. Integrating each exponential gives the real-valued reading

$$
E_Y(N,T)=\sum_{m\ge1} b_Y(m)
  \left(\frac Nm\right)^2
  \operatorname{sinc}^2\!\left(\frac T2\log\frac mN\right),
\qquad \operatorname{sinc}(x)=\frac{\sin x}{x},\quad \operatorname{sinc}(0)=1.
$$

The target term contributes exactly $b_Y(N)$. Every other term is nonnegative, so one nearby level gives a lower bound on the full error. Lean proves convergence and the error bound for this displayed series. The triangular integral identity is the calculus step connecting the series to frequency averaging. [Lean definitions and proofs](../PrimeFactors/IndexCoefficientWindow.lean)

## How close is too close?

Choose a prime $R>Y$. The first multiple $m$ of $R$ above $N$ is at most $N+R$, and its surviving coefficient contains $1/R$. If $4R\le N$ and $TR\le N$, its multiplier in the display is greater than $1/2$. The full error therefore exceeds $1/(2R)$. Using a prime between $Y$ and $2Y$ gives the more general bound $E_Y(N,T)-b_Y(N)>1/(4Y)$ whenever $Y\ge1$, $8Y\le N$ and $2TY\le N$. When a multiple happens to lie closer, the bound holds to a greater height. For $N=527$, $R=11$, the next multiple is just one away. The exact target is $49/527$, and the error exceeds $1/22$ for all $0\le T\le527$. [Lean bounds and numerical example](../PrimeFactors/IndexCoefficientWindow.lean)

For a 2,048-bit product with two 1,024-bit primes, set $Y=1000$ and $R=1009$. At every $T\le2^{2037}$ with $T\ge0$, the error exceeds $12/N$. Multiplying by $N$ leaves more than 12 units of error in the recovered factor sum. Twelve is half the widest spacing of 24 supplied by the project's elementary factor-sum congruence. [Full-size theorem](../PrimeFactors/IndexCoefficientWindow.lean) · [Factor-sum spacings](../PrimeFactors/CyclotomicRadixLift.lean)

A finite selection of frequencies can have the same problem. Take nonnegative weights totaling one, with all frequencies between $-T/2$ and $T/2$, and use the squared magnitude of their weighted sum of phases. If $m$ is within $H$ above $N$, $5H\le N$, and $TH\le N$, the contribution from a prime $R>Y$ dividing $m$ again exceeds $1/(2R)$. This sparse-window result holds for any number of frequencies and any placements in that band. [Sparse-window theorem](../PrimeFactors/IndexCoefficientWindow.lean)

Here $T$ is a bound on the imaginary arguments used by the reading. Turning a height into a running time would require a specific integration rule and a cost for evaluating the series to the required precision. The proof relies on the nonnegative squared window. A signed estimate could cancel contributions from neighboring levels and would require its own error analysis.
