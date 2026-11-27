# How many products split on the first multiplier-six test?

Assume the Riemann hypothesis (RH). More than $2^{1509}$ distinct 2,048-bit products of two 1,024-bit primes split on the first square test at multiplier six. The test takes the public product $N$, computes $S=\lceil\sqrt{24N}\rceil$, and checks whether $S^2-24N$ is a square. For this family the gcd of $N$ with $(S+\sqrt{S^2-24N})/2$ gives a prime factor. This takes two integer square roots and one gcd. The estimate counts a narrow family of prime ratios. For uniformly chosen eligible prime pairs, the project's upper bound for even a much longer multiplier-six search is below one success in $2^{469}$. [Lean proof](../PrimeFactors/MeanSquarePrimePartners.lean) · [Population upper bound](sharing-square-tests-across-factor-ranges.md#how-often-can-this-approach-find-the-actual-prime)

## Which primes contribute?

Write $U=2^{1024}$ and $H=2^{512}$. Take a smaller prime $p$ in $[79U/128,82U/128]$. Look at primes $q$ in $(3p/2,\,3p/2+H+1]$. Under RH, **fewer than $2^{542}$ of these smaller primes have fewer than $2^{501}$ partners**. The interval contains more than $2^{1009}$ smaller primes, so the exceptional fraction is below $2^{-467}$. This fraction describes the smaller primes that have many suitable partners. Supplying $N$ already fixes both factors. [Explicit mean-square estimate, Theorem 1](https://arxiv.org/pdf/2206.00433#page=2) · [Macroscopic interval count](factoring-more-products-at-the-same-budget.md#how-many-such-products-exist)

For every one of these pairs $p<q<U$ and $9U^2/16\le pq\le5U^2/8$. Put $S=3p+2q$ and $d=2q-3p$. The identity $S^2=24pq+d^2$ gives the upper bound $24pq\le S^2$. Here $0<d\le2H+2$ and $S\ge3U$. Consequently $d^2+1<6U\le2S$, so $(S-1)^2<24pq$. These two inequalities force the public starting label to equal $S$. In fact $(S+d)/2=2q$, whose gcd with $pq$ is $q$. All partners in this strip also miss the 33 ordinary candidate sums in the 34-root comparison. The existing wider-strip bound puts $p+q-2\sqrt{pq}=(\sqrt q-\sqrt p)^2$ beyond the entire ordinary prefix. [First-label theorem](../PrimeFactors/MeanSquarePrimePartners.lean) · [Wider-strip bound](../PrimeFactors/InteriorBatchPopulation.lean) · [Ordinary and switched schedules](switching-after-sixteen-tests.md)

## How an integral counts individual primes

Let $\theta(x)=\sum_{r\le x,\ r\ \mathrm{prime}}\log r$, using natural logarithms. Cully-Hugill and Dudek prove under RH that, for $X\ge10^8$ and $0<\delta\le10^{-8}$,
$$
\int_1^X \bigl(\theta(t+\delta t)-\theta(t)-\delta t\bigr)^2\,dt
< 202\delta X^2(\log X)^2.
$$
The theorem uses $\theta$ directly, so each term counts one prime. The choices $X=U$ and $\delta=1/H$ satisfy both numerical restrictions. [Cully-Hugill and Dudek, Theorem 1](https://arxiv.org/pdf/2206.00433#page=2) · [Journal publication](https://www.cambridge.org/core/journals/journal-of-the-australian-mathematical-society/article/an-explicit-meanvalue-estimate-for-the-prime-number-theorem-in-intervals/F9D260ADEA6E86ED47F2B5EB5469F727)

For each smaller prime $p$ with fewer than $2^{501}$ partners, take the real interval $I_p=[3p/2,3p/2+1)$. Every $t\in I_p$ satisfies $7U/8\le t\le U$. Its entire prime-counting window $(t,t+\delta t]$ lies inside the partner interval for $p$. Each prime weighs at most $\log(2U)<768$, giving a total weight below $768\cdot2^{501}$. Meanwhile $\delta t\ge 7H/8$. Their difference is at least $2^{511}$. Each interval therefore contributes at least $2^{1022}$ to the integral. Distinct integers $p$ have centers at least $3/2$ apart, so their unit intervals are disjoint. Summing the lower bounds and using $202<2^8$ and $\log U<2^{10}$ gives
$$
\#\{\text{exceptional }p\}\ <\frac{202\,2^{-512}\,2^{2048}(\log U)^2}{2^{1022}}<2^{542}.
$$

Removing these exceptions leaves more than $2^{1008}$ eligible smaller primes. Each has at least $2^{501}$ partners. Unique factorization ensures that the ordered pairs give distinct product integers. Lean proves the discretization, the first-label identity and the lower bound for the repository's finite set of successful inputs. It takes the published integral estimate and the fixed macroscopic prime count as explicit premises. The latter follows unconditionally from the previously documented Rosser–Schoenfeld endpoint bounds. RH enters through the integral estimate. [Machine-checked implications](../PrimeFactors/MeanSquarePrimePartners.lean) · [Rosser and Schoenfeld, Theorem 2](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6)

An unconditional numerical exception bound at this particular bit length remains open in this analysis. Bazzanella gives unconditional asymptotic estimates for exceptions between consecutive squares. That theorem uses centers of the form $n^2$ and asymptotic constants. Applying it to $3p/2$ at this fixed $U$ would need an additional argument and numerical constants. [Bazzanella, *Primes between consecutive squares*](https://iris.polito.it/bitstream/11583/1397858/2/Primes-between-squares.pdf)
