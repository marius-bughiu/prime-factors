# When does the first square test have a prime partner?

Let $U=2^b$ and take every prime $p$ between $79U/128$ and $82U/128$. As $b$ grows, **almost every such prime has a larger $b$-bit prime partner $q$ for which one square test splits $pq$**. The result is unconditional. It counts choices for the partner of a prescribed smaller prime. A randomly chosen partner has far more possibilities than this narrow range. The estimates below contain unspecified constants and give no numerical fraction at $b=1024$. [Finite Lean reduction](../PrimeFactors/PrimeGapPopulation.lean) · [Järviniemi, Theorem 1.1](https://arxiv.org/pdf/2212.10965#page=1)

## The one-test search

Given only $N$, compute $S=\lceil\sqrt{24N}\rceil$ and check whether $S^2-24N$ is a square. If the square root is $z$, take $\gcd(N,(S+z)/2)$. This uses two integer square roots counting the setup. Put $c=\lfloor3p/2\rfloor$ for the proof. Every prime $q$ with $c<q\le c+\lfloor\sqrt c\rfloor$ gives
$$
(3p+2q)^2-24pq=(2q-3p)^2\le4c\le 6p.
$$
Since $2(3p+2q)-1>6p$, the preceding integer has square strictly below $24pq$. The search therefore tests the exact sum $3p+2q$ first, and its gcd gives a genuine prime factor. In the prescribed $p$ interval, $q$ has $b$ bits and $9U^2/16\le pq\le5U^2/8$ for all sufficiently large $b$. [First-trace and gcd proof](../PrimeFactors/PrimeGapPopulation.lean)

For example, start with $N=40{,}913$. The first integer above $\sqrt{24N}$ is $991$. Its square leaves $991^2-24N=169=13^2$, so $\gcd(40{,}913,(991+13)/2)=251$. Division gives the other prime, $163$. Both factors have eight bits.

## Why few smaller primes lack a partner

Suppose that interval has no prime. Let $r$ be the last prime at or before $c$, and let $s$ be the next prime. Then $r\le c<s$ and $s-r>\sqrt r$. Each failed $p$ gives a different integer $c$ because $p\mapsto\lfloor3p/2\rfloor$ is injective. The gap $[r,s)$ can account for at most $s-r$ such integers. Lean bounds the exact number of misses by the sum of the lengths of these long gaps starting at primes $r\le U$. [Finite counting theorem](../PrimeFactors/PrimeGapPopulation.lean)

Heath-Brown’s unconditional Theorem 1 bounds this sum by $O_\varepsilon(U^{3/5+\varepsilon})$. Järviniemi’s Theorem 1.1 improves the exponent to $0.57+\varepsilon$ on each interval $[X,2X]$ with gaps at least $\sqrt X$. Splitting $[2,U]$ into dyadic intervals and summing the geometric series gives the same improved exponent for our sum. The prime number theorem gives $(3/128+o(1))U/\log U$ eligible smaller primes. Their missing fraction is consequently $O_\varepsilon(U^{-0.43+\varepsilon}\log U)$. The transfer from these published analytic results is a written argument. [Heath-Brown, Theorem 1](https://arxiv.org/pdf/1906.09555#page=1) · [Järviniemi, Theorem 1.1](https://arxiv.org/pdf/2212.10965#page=1)

## How many partners can the test recover?

Heath-Brown’s Theorem 2 also controls the prime **count** on intervals of length at most $\sqrt y$. Its exceptional set has real measure $O_\varepsilon(U^{3/5+\varepsilon})$ up to $2U$. This measure bound can be used at our discrete centers. For each center $c$, take the interval $[c,c+1/4]$. Moving the start in this interval and using length $\sqrt y$ changes each endpoint of $(c,c+\lfloor\sqrt c\rfloor]$ by less than two units. The prime counts and logarithmic integrals therefore change by $O(1)$. Centers whose error exceeds twice the theorem’s threshold $\sqrt c/(\log c\log\log c)$ each give a disjoint quarter-unit interval in the exceptional set for sufficiently large $U$. All but $O_\varepsilon(U^{3/5+\varepsilon})$ eligible smaller primes consequently have
$$
(1+o(1))\frac{\sqrt{3p/2}}{\log(3p/2)}
$$
prime partners inside the one-test interval, uniformly there. [Heath-Brown, Theorem 2](https://arxiv.org/pdf/1906.09555#page=2)

Writing $\alpha=79/128$, $\beta=82/128$, this gives an asymptotic for the number of distinct products in that particular strip. Sum over $p$ by the prime number theorem. The exceptional centers contribute at most $O_\varepsilon(U^{1.1+\varepsilon})$ products by interval length alone. For any fixed $0<\varepsilon<0.4$ the result is
$$
\left(\tfrac23\sqrt{3/2}\,(\beta^{3/2}-\alpha^{3/2})+o(1)\right)
\frac{U^{3/2}}{(\log U)^2}.
$$
The full balanced product population in the public bin grows on the scale $U^2/(\log U)^2$. Thus the proportion contributed by this strip decays on the scale $U^{-1/2}$, even while almost every eligible smaller prime acquires a partner. Neither the published asymptotic gap estimate nor this argument supplies a usable numerical threshold at 2,048 product bits. The explicit mean-value estimate of Cully-Hugill and Dudek assumes the Riemann hypothesis. [Explicit conditional estimate](https://arxiv.org/abs/2206.00433)
