# Which powers could reveal the prime sum?

The two inputs where 106 guesses each failed raised a bigger question. Would trying many more guesses of the same kind help? For our continued-fraction search, the answer can now be bounded across the entire population of balanced 2,048-bit prime products.

* For **each fixed product**, fewer than one in $2^{1295}$ integers $E$ chosen uniformly from 1 through $N$ can reveal its factorization this way.
* For **uniformly chosen products** of two distinct 1,024-bit primes with a 2,048-bit product, fewer than one in $2^{553}$ can be solved by this search with **any** $1\le E\le N$ whose prime factors are all at most 1,500. Even a choice tailored to the particular product is covered. Every tested prefix least common multiple falls in this family.

Success here means the exact fraction $E/((p-1)(q-1))$ occurs in the continued fractions of $E/N$. These results limit two strategies for choosing $E$. They leave open how to choose a successful exponent using other information in the product. Prime pairs are counted once with the smaller prime first. [Uniform exponent count](../PrimeFactors/SuccessfulExponentCount.lean) · [All smooth exponents on the eligible population](../PrimeFactors/SmoothConvergentPopulation.lean) · [Experiments on the two full-size inputs](testing-lcm-prefixes-at-the-product-width.md)

## The arithmetic behind both counts

Write $F=(p-1)(q-1)$, $D=N-F=p+q-1$, and $g=\gcd(E,F)$. The denominator of $E/F$ in lowest terms is $F/g$. Legendre’s approximation theorem and the error bound for an actual convergent give two thresholds,

$$
2EFD<Ng^2\quad\Longrightarrow\quad E/F\text{ occurs}
\quad\Longrightarrow\quad EFD<Ng^2.
$$

For $143=11\times13$, both $E=20$ and $E=24$ are between the thresholds. Only 24 works. The distinction is measurable even on a small example. [Proofs and checked transition cases](../PrimeFactors/ConvergentGcdThreshold.lean)

There is an exact test in the gap. Write $a/b=E/F$ in lowest terms. Choose the unique $d$ from 1 through $b$ for which $ad=bc+1$ for some integer $c$ (use $d=1$ when $b=1$). Then $E/F$ occurs precisely when

$$aD(b+d)<N.$$

Equality gives a miss. For $N=143$, the left side is 161 for $E=20$ and 138 for $E=24$. This explains why one guess succeeds. To use the test we need a candidate for $F$, which already determines the prime sum $N-F+1$. How to choose a successful $E$ using the product alone remains open. [Exact equivalence and three checked boundary examples](../PrimeFactors/FareyParentCriterion.lean)

If the fraction occurs then its numerator $a=E/g$ satisfies both $aFD<Ng$ and $ag\le N$. Consequently $a^2FD<N^2$. For the specified prime widths this forces $a<2^{512}$. Every successful exponent is determined by such an integer $a$ and a divisor $g$ of $F$. The project’s earlier divisor-count theorem bounds the number of divisors of $F$ by $2^{240}$. Together these give fewer than $2^{752}$ successful choices among at least $2^{2047}$ possible exponents. This calculation uses no model for the distribution of the primes. [Finite counting proof](../PrimeFactors/SuccessfulExponentCount.lean) · [Divisor-count bound](../PrimeFactors/UniformDivisorCount.lean)

## Why changing the small-prime menu is unlikely to help

The remainder test also gives $D\le N\bmod E<E$. Combined with the necessary inequality above, this implies $g^2>2N$ for primes at least six. Thus a successful exponent composed of primes at most 1,500 would require $F$ to have an exceptionally large divisor composed of those same small primes. The entire menu is covered by a single condition on $F$. [Gcd threshold and connection to prefix least common multiples](../PrimeFactors/LcmConvergentObstruction.lean)

To bound how often this occurs, split a large smooth divisor of $F$ into $xy$ with $x\mid p-1$ and $y\mid q-1$. There are at most $2^{1024}/x$ multiples of $x$ and $2^{1024}/y$ multiples of $y$ in the respective ranges. On the event $xy\ge 2^{1024}$ we have $(xy)^{3/4}\ge 2^{768}$. Weighting by $(xy)^{3/4}$ leaves $x^{-1/4}y^{-1/4}$ in the sum. Each predecessor contributes a finite Euler product bounded by $2^{94}$. Lean checks fourth-power inequalities for the rational estimates of all 239 primes up to 1,500 and checks their product. A lower count of eligible prime pairs supplies the denominator. The proof uses no assumption about zeta zeros. [Counting smooth divisors of the two predecessors](../PrimeFactors/SmoothTotientTail.lean) · [Euler-product certificate](../PrimeFactors/SmoothTotientEuler.lean) · [Eligible population size](../PrimeFactors/ChebyshevPrimeSample.lean)
