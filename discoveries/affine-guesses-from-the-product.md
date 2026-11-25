# When a guess depends on the whole product

Suppose we read the product $N$ and choose two integers $a,b$, each with magnitude below $2^{40}$. We try $e=aN+b$ and get to inspect **every divisor** of $(N+1)^2+Ne^2$ for free. Even if we try *all* such choices, the actual factor sum appears on fewer than **one in $2^{288}$** of the target products. The targets are the 2,048-bit products of two distinct 1,024-bit primes, with each unordered pair counted once. This bound includes lucky hits where $e$ differs from the signed difference of the modular inverses. [Lean theorems](../PrimeFactors/AffineInverseGap.lean) · [An example of a lucky hit](which-inverse-guesses-can-work.md)

| Bound on each coefficient magnitude | One fixed rule $aN+b$ | All allowed rules, including choices made after seeing $N$ |
| --- | ---: | ---: |
| Below $2^{16}$ | Fraction $<2^{-375}$ | Fraction $<2^{-341}$ |
| Below $2^{40}$ | Fraction $<2^{-370}$ | Fraction $<2^{-288}$ |

With nonzero $a$, the magnitude of $aN+b$ is at least $N-|b|$, already larger than the actual inverse difference on these products. The remaining question is whether the wider divisibility test can find the sum accidentally. For both rows of the table, the value of $e$ can use all the digits of $N$ and can be larger than $N$. [Magnitude and population bounds](../PrimeFactors/AffineInverseGap.lean)

## Why a product-dependent guess still constrains the partner

Fix the smaller prime $p$ for counting purposes. For every possible partner $q$ the product $N=pq$ is congruent to $-p^2$ modulo the sum $S=p+q$. Every integer polynomial preserves congruences. Therefore, for a fixed polynomial $f$, the test $S\mid(N+1)^2+Nf(N)^2$ has exactly the same outcome if we replace $f(N)$ by $g=f(-p^2)$. Reducing the other occurrences of $N$ then shows that every successful $S$ divides

$$M_p=\left|(p^2-1)^2-p^2g^2\right|
=\left|(p^2+pg-1)(p^2-pg-1)\right|.$$

This integer is independent of $q$. Neither factor vanishes, since each has remainder $-1$ modulo $p$. Every positive divisor of $M_p$ specifies at most one partner $q=S-p$. The substitution holds for every fixed degree. The numerical estimates in the table are for degree at most one. The hidden prime is used to prove the count and is never supplied to the proposed test. [Polynomial substitution and row bounds](../PrimeFactors/AffineInverseGap.lean)

For $f(X)=aX+b$ put $C=2^t$ and $U=2^{1024}$. Since $1<p<U$, we have $p^2+1\le U^2$, $|g|\le C U^2$, and both $p^2-1$ and $|pg|$ are strictly below $CU^3$. The absolute difference of their squares is therefore below $2^{6144+2t}$. The repository's divisor estimate $\tau(m)^{336}\le2^{14882}m^{32}$ gives $\tau(M_p)\le45\cdot2^{627}$ at $t=16$ and $\tau(M_p)\le17\cdot2^{633}$ at $t=40$. Multiply by the number of possible smaller primes and, for the final column, by fewer than $2^{2t+2}$ choices of coefficients. This counts the union of all successes, so choosing coefficients from the permitted set after reading $N$ is included. [Divisor estimate](../PrimeFactors/UniformDivisorCount.lean) · [Finite comparisons](../PrimeFactors/AffineInverseGap.lean)

The ratio of the number of candidate smaller primes to the number of target products is below $44331/2^{1023}$. The Lean fraction theorems take this ratio as an explicit hypothesis. The project derives it from published prime counts and checks the remaining arithmetic in Lean. [Derivation of the population ratio](stride-budget.md#an-explicit-bound-at-exactly-2048-bits) · [Rosser and Schoenfeld, Corollary 1](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6)

## Which choices change the argument?

A reduction modulo another integer can discard precisely the congruence used here. For $N=15$, $p=3$ and $S=8$, taking $e=N\bmod11$ gives 4 and the sum divides $16^2+15\cdot4^2=496$. Substituting $-p^2$ before reducing modulo 11 gives 2, and 8 fails to divide $16^2+15\cdot2^2=316$. A small fixed output range can still be counted by a fixed list of guesses. A quotient or remainder with a large output range, coefficients outside the bounded set, or a different criterion for identifying the sum needs its own population estimate. [Checked remainder example](../PrimeFactors/AffineInverseGap.lean) · [Fixed-list estimate](which-inverse-guesses-can-work.md)
