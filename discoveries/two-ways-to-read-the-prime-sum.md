# Two ways to read the prime sum

Knowing the sum of two primes turns factoring into a square-root calculation. For example, if the product is 9,017 and the sum is 198, the squared distance between the primes is $198^2-4\cdot9017=3136$. The primes are $(198-56)/2=71$ and $(198+56)/2=127$. The question is how to get the sum when the product is all we have.

## One digit of a polynomial

Let $\Phi_N$ be the cyclotomic polynomial indexed by the public product $N$. At $N=9017$, evaluating that polynomial at 9 gives remainder **17** on division by 64. In base eight the remainder is written **21**, so its upper digit is 2. This tells us that the sum of the factors is 6 modulo 16. The factors are both seven bits wide. The possible sum lies from 190 through 205 using the proved width bound, so 198 is the only possibility. [Lean proof and numerical example](../PrimeFactors/CyclotomicSumDigit.lean)

For $N=pq$ with distinct primes, the polynomial has value 1 at 1 and derivative $(p-1)(q-1)/2$ there. Consequently, modulo $M^2$, its value at $1+M$ is $1+M\,(p-1)(q-1)/2$. One upper digit gives the sum modulo $2M$. For two 1,024-bit primes, $M=2^{1020}$ suffices to locate the exact sum in the interval above $2\sqrt N$. [Derivative literature](https://arxiv.org/abs/1805.05207) · [Local modular decoder](../PrimeFactors/CyclotomicSumDigit.lean)

The missing step is computing that digit from $N$. Computing the whole integer value first takes more than $(p-1)(q-1)\log_2 M$ output bits. Reading the polynomial's coefficients in order also has a concrete cost. From degree two up to the smaller prime $p$, the first nonzero coefficient occurs at degree $p$ itself. Both observations leave open the possibility of a faster direct modular evaluation. Given the primes, the modular value takes just the arithmetic in the formula above. [Output size and first nonzero coefficient](../PrimeFactors/CyclotomicSumDigit.lean)

## Counting consecutive integers

Imagine numbering $N$ positions in a circle and looking at a run of $t$ consecutive numbers from each starting point. Count the runs that contain no multiple of either prime. For $1\le t\le p<q$, this count is exactly $C=(p-t)(q-t)$. This follows because a run misses the multiples of $p$ at $p-t$ possible starting residues modulo $p$, and likewise for $q$. The Chinese remainder theorem combines the two counts. Hence $t(p+q)=N+t^2-C$. An estimate of $C$ with absolute error strictly less than $t$ still gives the exact sum by rounding to the nearest even integer. [Count and integer rounding proof](../PrimeFactors/UnitRunCounts.lean)

For $143=11\cdot13$ and $t=6$, exactly 35 of the 143 runs avoid both primes, 72 encounter just one, and 36 encounter both. The count 35 gives the sum $(143+36-35)/6=24$. Determining the count cheaply for an unknown full-size pair remains open. Trying one randomly placed run with up to $2^{40}$ terms has less than a $2^{-982}$ chance of encountering exactly one prime when both factors have 1,024 bits. A length chosen to make that chance exceed one half uses more than $2^{1022}$ consecutive terms. These are counts of terms in the direct product. They do not bound faster algorithms for evaluating factorial products. [Exact odds and deterministic interval comparison](../PrimeFactors/UnitRunCounts.lean)
