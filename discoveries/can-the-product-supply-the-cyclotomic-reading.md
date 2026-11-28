# Can the product supply the cyclotomic reading?

A sufficiently accurate value of $T_N(x)=(x-1)\Psi_N(x)$ at $x=\exp(-1/(8B))$ identifies the sum of the two prime factors. Here $B\le p<q<2B$ and $N=pq$. The product gives us a cheap approximation to try: replace both unknown primes by $\sqrt N$. We also examined an expansion whose coefficients can be calculated using greatest common divisors. [What accuracy is needed](which-cyclotomic-measurements-distinguish-the-prime-sum.md)

## Substituting two equal factors

The equal-factor estimate is $(1-\exp(-\sqrt N/(8B)))^2$. If it meets the sufficient absolute tolerance for the decoder ($1/(8192B)$), Lean proves

$$p+q-2\sqrt N\le 81/256.$$

The midpoint $(p+q)/2$ is an integer for odd primes. That inequality forces it to be the first integer at or above $\sqrt N$. Fermat’s first square test therefore already gives the two primes whenever this approximation is accurate enough. The converse fails. On $551=19\cdot29$ the first midpoint is 24 and $24^2-551=25$, yet the equal-factor approximation misses the tolerance. [Error bound and counterexample](../PrimeFactors/CyclotomicDiagonalEstimate.lean)

In the other direction, a deficit $p+q-2\sqrt N\le1/64$ guarantees that tolerance. A sufficient condition in terms of the primes is $(q-p)^2\le B/16$. For the deliberately selected $10{,}403=101\cdot103$ with $B=64$, the gap reaches this threshold exactly. The estimate succeeds and the first midpoint, 102, gives $102^2-10{,}403=1$. [Sufficiency and the 10,403 control](../PrimeFactors/CyclotomicDiagonalSufficiency.lean)

How often does the estimate reach the tolerance? Among all unordered pairs of distinct 1,024-bit primes with a 2,048-bit product, the fraction lies strictly between $2^{-517}$ and $2^{-500}$. The lower bound counts pairs of primes in the same interval of width $2^{509}$ high enough in the range to guarantee a 2,048-bit product. It allows the prime counts to vary freely between intervals. The upper bound counts how many possible partners each large prime can have under the necessary gap bound. Even trying the first $2^{40}$ consecutive Fermat midpoints gives a sum compatible with a common accurate reading for fewer than one in $2^{479}$ eligible pairs. [Finite counting proofs](../PrimeFactors/CyclotomicDiagonalPopulation.lean)

## What a logarithmic derivative sees

For distinct primes, $T_N(X)=(1-X^p)(1-X^q)$. Formally expand $-XT'_N(X)/T_N(X)$. At each positive index $m$, its coefficient is

$$p\,\mathbf{1}_{p\mid m}+q\,\mathbf{1}_{q\mid m}.$$

If $N$ does not divide $m$, computing $\gcd(m,N)$ supplies that coefficient. A gcd of one gives zero, and any other gcd here is already one of the prime factors. At a positive multiple of $N$ the coefficient is the unknown sum $p+q$. Treating that last quantity as a free reading would assume precisely the missing information. For 551, the coefficients at indices 18, 38, 58 and 551 are 0, 19, 29 and 48. [Formal-series identity and gcd classification](../PrimeFactors/CyclotomicLogCoefficients.lean)

This also explains what happens with samples taken away from multiples of $N$. If a weighted sum of sampled coefficients at positive indices below $N$ is nonzero, a gcd at one of those indices already gives a prime. For 32,881 the first 128 gcd tests give only ones. The first 251 tests encounter both 131 and 251. This statement allows arbitrary integer weights and choices of indices. [Sample theorem and both numerical checks](../PrimeFactors/CyclotomicLogCoefficients.lean)

The logarithmic expansion is related to the classical formula for $\log\Phi_N$ in terms of Ramanujan sums. For this particular polynomial, all the individual indices coprime to $N$ cancel exactly. Bounds for primes in coprime residue classes do not by themselves evaluate the surviving terms for a specified product. [Tóth, Theorem 1](https://arxiv.org/pdf/1002.3221#page=2) · [Pinned statements on Dirichlet functions](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)

## How far must a dense logarithmic sum run?

Below $N$, use $w_N(m)=0$ when $\gcd(m,N)=1$ and $w_N(m)=\gcd(m,N)$ otherwise. A reference calculation using only the product and word size is

$$A_K=\exp\!\left(-\sum_{m=1}^K w_N(m)\,\frac{e^{-m/(8B)}}m\right),\qquad K<N.$$

The Taylor series for $-\log(1-z)$ explains the convergence. One sequence of positive terms comes from multiples of $p$ and the other from multiples of $q$. Omitting both tails overestimates $T_N(x)$. Their first omitted terms give a lower bound on the error, and geometric sums give an upper bound. [Formal coefficient bridge and lower bound](../PrimeFactors/CyclotomicLogTail.lean) · [Upper bound](../PrimeFactors/CyclotomicLogUpper.lean)

For any two distinct 1,024-bit primes and $B=2^{1023}$, the degree cutoffs are enormous even in exact arithmetic:

| Last degree included | Accuracy of the raw sum |
| --- | --- |
| $K\le2048B=2^{1034}$ | Error strictly exceeds the certified tolerance of $1/(8192B)$. |
| $K=5768B$ | Error is strictly below $1/(8192B)$. This cutoff is below $N$, so the gcd formula applies to every term. |

These bounds compare the exact real sum with a tolerance that guarantees unique decoding. A larger error can still select the right sum on an individual product. Computing the terms at finite precision and estimating the omitted tail each require a separate error bound. A dense calculation reaches the first proper gcd at index $p$, long before the readings enter the certified precision range. A different way to sum nonconsecutive terms or rigorously correct the tail would have to account for its own cost. [Both bounds for the product-only expression](../PrimeFactors/PublicCyclotomicLogReading.lean)

## Can one correction cover every product?

Suppose that for each word size $B$ and cutoff $K$ we may choose any real number $c$, even with unlimited work beforehand. Replace the raw reading $A_K$ by $A_K e^{-c}$ to correct the omitted logarithmic tail. For every $K\le5500B$ at $B=2^{1023}$, Lean proves there are two eligible products sharing their larger prime for which **every** such correction misses the sufficient tolerance on at least one. The two products can depend on the cutoff. At $5768B$, the uncorrected exact sum already suffices for every pair. The ratio of these cutoffs is less than 1.049. [Common-correction lower bound](../PrimeFactors/CyclotomicCommonTailCorrection.lean) · [Uniform upper bound](../PrimeFactors/PublicCyclotomicLogReading.lean)

The proof finds two smaller primes far apart but having the same integer quotient when $K$ is divided by them. Their logarithmic tails start at the same term number. Every term changes in the same direction, so the first omitted term alone proves the two corrections they need are too far apart. The count uses an elementary lower bound on the number of primes in a subinterval. At $B=16$ and $K=31$, the same incompatibility already holds for $551=19\cdot29$ and $667=23\cdot29$. Corrections calculated separately from each product remain an open route. [Separation, prime count and small control](../PrimeFactors/CyclotomicCommonTailCorrection.lean)
