# How often can a random integer reveal a factor?

Take a positive integer at random and compute its greatest common divisor with the product. Suppose small integers are at least as likely as large ones. Even with the best possible choice of such probabilities, a single draw has **less than one chance in $2^{1022}$** of finding a factor of a product of two distinct 1,024-bit primes. We can describe a distribution that attains the exact maximum for each individual product. Calculating it by the formula below uses the hidden primes. [Lean proof](../PrimeFactors/MonotoneDivisorSampling.lean)

For example, if the product is 77, the best choice is to draw uniformly from 1 through 56. Exactly 13 of those 56 integers share a proper factor with 77. Even a distribution that puts some weight on arbitrarily large numbers cannot beat $13/56$ under the stated rule. Counting the hits directly from 77 first encounters a factor at 7. The exhaustive count explains the probability and costs more than finding the first factor. [Product-only experiment](../experiments/monotone_divisor_sampling.py) · [Checked examples and cutoff](../benchmarks/monotone-divisor-sampling.json)

## The exact maximum

Write $N=pq$ for distinct primes. Let $u$ be the least positive inverse of $p$ modulo $q$, let $v$ be the least positive inverse of $q$ modulo $p$, and set $K=\max(u,v)$. The maximum probability is

$$
R=\frac{p+q-1/K}{N}.
$$

If $u\ge v$, the uniform distribution on $1,\ldots,pu$ attains it. Otherwise use $1,\ldots,qv$. Both cutoffs are below $N$. A way to compute *any* positive maximizing cutoff directly from $N$ would give a factor by one gcd. Indeed, if its last index contributes no hit, dropping that index strictly increases the positive hit fraction. Knowing $NR$ to error strictly below $1/2$ also determines the sum for odd primes. Add $1/2$ to the estimate and round to the nearest even integer. The sum and product determine the two roots. The difficulty is obtaining this much information from the product. [Optimality, equality cases and rounding](../PrimeFactors/MonotoneDivisorSampling.lean)

Here is why even an uneven distribution cannot do better. The number of proper hits through the positive integer $m$ is

$$
C(m)=\left\lfloor m/p\right\rfloor+\left\lfloor m/q\right\rfloor-2\left\lfloor m/N\right\rfloor.
$$

Subtracting twice removes multiples of $N$, whose gcd is the whole input. For $r=m\bmod p$ and $s=m\bmod q$, subtracting $NC(m)$ from $(p+q)m$ leaves $qr+ps+2N\lfloor m/N\rfloor$. The nonnegative integer $qvr+pus$ agrees with $m$ modulo both primes. Consequently $m\bmod N\le qvr+pus\le K(qr+ps)$. Together these give $C(m)\le mR$. At $m=pu$ the two remainders are zero and one. The bound is attained when $K=u$. Interchanging the primes gives the other case.

Summation by parts transfers the prefix inequality to all nonnegative decreasing weights on positive integers. Taking limits covers probability distributions with infinite support. In particular $R<1/p+1/q\le 2^{-1022}$ at the target size. If at each attempt, conditional on its history, the next draw still has decreasing probabilities, summing the first-hit probabilities gives a chance of success below $T2^{-1022}$ after $T>0$ draws. A one-half chance thus requires more than $2^{1021}$ draws in this model. The finite bound, its sharpness, and the infinite-support limit are checked in Lean. The repeated-draw corollary uses the union bound.

## Connection with the Riemann repository

For real $s>1$, one proposed way to sample coefficients of the principal Dirichlet series is to draw positive integers with probabilities proportional to $x^{-s}$. Under these probabilities the chance of divisibility by $d$ is $d^{-s}$, by summing over its multiples. The chance of a proper gcd here is therefore $p^{-s}+q^{-s}-2N^{-s}$. An imaginary height changes the phase of a summand while preserving these sampling weights. The sharp bound above includes every finite truncation and every decreasing reweighting. Estimating a different aggregate, choosing queries concentrated around product-dependent locations, or evaluating the whole analytic function by another method has a different cost question. [Golomb’s zeta distribution](https://doi.org/10.1016/0022-314X(70)90018-1) · [Pinned Dirichlet statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean) · [Which boundary readings would suffice](factor-recovery-from-boundary-readings.md)

We tested the formula exhaustively on the 153 unordered pairs of distinct primes below 62, examining every positive cutoff through two periods. This covers both choices of inverse in the formula. On $221=13\times17$, the highest fraction was $23/170$, and the first proper gcd occurred at 13. The bounded control on 77 stopped at 6 with all six probes coprime and the cofactor 77 unresolved. [Reproducible census](../tests/test_monotone_divisor_sampling.py) · [Published benchmark rows](../benchmarks/monotone-divisor-sampling.json)

For two independent guesses we can now compute the exact maximum for their sum and, under equal distributions, their difference. A way to locate a best pair of prefix lengths for the sum would give a factor directly. [Two-draw proofs and examples](adding-and-subtracting-random-guesses.md)
