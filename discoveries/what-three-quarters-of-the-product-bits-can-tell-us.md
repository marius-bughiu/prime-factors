# What three quarters of the product bits can tell us

Suppose we hide the middle 512 bits of a 2,048-bit product and keep its top 1,024 and bottom 512 bits. A rule sees those bits and may name up to $2^{40}$ possible sums of the two primes, just over a trillion guesses. **Fewer than one in $2^{434}$ eligible prime pairs has its true sum anywhere on the list**, however the rule chooses the list. Giving it the project's five-field search-interval record as well raises the bound to fewer than one in $2^{426}$. Both bounds are unconditional. [Lean theorems](../PrimeFactors/HighLowSumPopulation.lean)

The population consists of all pairs of distinct 1,024-bit primes with a 2,048-bit product, counted once with the smaller prime first. The rates are fractions of this finite population, so they also apply to a pair drawn uniformly from it. Guessing the right sum matters because its square minus four times the product equals the square of the difference between the primes. This result limits rules using the specified readings. A factoring method with access to the complete product can also use its middle bits and adapt its search to observations derived from them. [Recovering factors from the sum](../PrimeFactors/FactorSum.lean)

## A small example with identical readings

The two products below each have 20 bits and two 10-bit prime factors. Their upper ten bits are identical, as are their lower five bits and all five interval readings.

| Product | Prime factors | Correct sum |
|---:|---|---:|
| 546,673 | 563 × 971 | 1,534 |
| 546,577 | 619 × 883 | 1,502 |

The high word is 533 and the low five bits represent 17. Both products have a square root that rounds up to 740. Dividing either product by 512 or 1,023 and rounding down gives 1,067 or 534, respectively. Both leave remainder 1 modulo 24. A rule seeing these values must return the same list for both, so a single guess cannot cover both pairs. The full-size bounds allow a much longer list. [Checked example](../PrimeFactors/HighLowSumPopulation.lean)

## Why the low bits matter in the count

Consider two pairs $(p,q)$ and $(a,b)$ with the same sum and the same low $k$ product bits. The identity $ab-pq=(a-p)(q-a)$ says that $2^k$ divides the product on the right. Write $q-p=2^v g$ with $g$ odd. Since the two terms $a-p$ and $q-a$ add to $q-p$, at least one contains at most $v$ factors of two. The other must be divisible by $2^{k-v}$ when $v<k$. Thus the proposed smaller factor $a$ must agree with either $p$ or $q$ modulo $2^{k-v}$. For $v\ge k$ the proof uses modulus one. The loss of precision is real. The prime pairs $(73,83)$ and $(67,89)$ share sum 156 and the same low five product bits. The factor 67 agrees with 83 modulo 16 and with neither 73 nor 83 modulo 32. [Low-bit identity, converse and example](../PrimeFactors/HighLowSumPopulation.lean)

Now fix a high word, a low suffix, a proposed sum and the gap exponent $v$. Products with the same high word lie in an interval of width $B=2^{1024}$. Increasing the smaller factor by $t$ at fixed sum changes the product by at least $t$ times the gap of the later pair. For pairs whose gap divided by $2^v$ is at least $D=2^{512}$, moving the smaller factor by its allowed spacing takes the product outside this interval. Each of the two residue classes therefore contributes at most one such pair. For smaller gaps, the smaller factor and the gap divided by $2^v$ give at most $BD$ choices in each layer. [Product spacing](../PrimeFactors/ActualWindowAdvice.lean) · [Count across gap exponents](../PrimeFactors/HighLowSumPopulation.lean)

With $b$ possible gap exponents, $k$ low bits and at most $J$ guesses for each reading, the total number of pairs covered is at most $b(BD+2B\,2^kJ)$ whenever $B\le 2^kD$. Taking $b=1024$, $k=512$ and $J=2^{40}$ gives the first rate after division by the proven lower bound on the prime-pair population. For the second rate, the rule also sees the actual high word, rounded-up square root, two width quotients and remainder modulo 24. A fixed high word permits at most 288 such records. Combining their lists costs at most a factor of 288 in the list budget. The proof uses no unproved assumption about how primes are distributed among suffixes. [Interval readings](../PrimeFactors/ActualWindowAdvice.lean) · [Prime-pair denominator](../PrimeFactors/ChebyshevPrimeSample.lean)
