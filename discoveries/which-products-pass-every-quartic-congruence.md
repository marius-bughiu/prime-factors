# Which products pass every quartic congruence with a denominator?

Let $N=pq$ be a product of two odd primes. The equation $a^4+4b^4\equiv Nd^4\pmod m$ admits a locally primitive point for **every positive modulus** $m$ if and only if the primes and their product meet the following three conditions.

1. $p\equiv1\pmod4$.
2. $q\equiv1\pmod4$.
3. $N\equiv1$ or $5\pmod{16}$.

Here $d>0$, and for every prime dividing the current modulus, at least one of $a,b$ must be indivisible by that prime. This rules out satisfying a congruence just by setting all coordinates to zero. The coordinates and denominator may change with the modulus. The test at 16 is cheap to perform from $N$. The other two conditions involve the unknown factors. [Classification for every modulus and for semiprimes](../PrimeFactors/QuarticLocalClassification.lean)

## Why every modulus is covered

For an odd input, reducing a primitive point modulo 16 forces $a,d$ odd. Even and odd fourth powers are 0 and 1 modulo 16, respectively. This gives the two allowed classes. Conversely, every number equal to 1 modulo 16 has an odd fourth root at every power of 2. For an input equal to 5, choosing $b=1$ reduces the question to the preceding case. [Two-adic necessity and lifting](../PrimeFactors/QuarticTwoLocalPoints.lean)

At a prime $r\equiv1\pmod4$ a square root $i$ of $-1$ exists. The identity $(1+i)^4=-4$ gives a starting point with $b=1,d=r$. Its nonzero first coordinate lifts to every power of $r$ for any $N$. At a prime $r\equiv3\pmod4$ outside $N$, every square is a fourth power and every residue is a sum of two squares. A point with $d=1$ and at least one nonzero numerator coordinate lifts as well. If instead $r$ divides $N$, the equation would force both numerator coordinates to vanish modulo $r$, which violates the stated requirement. The Chinese remainder theorem combines independent points at the prime powers. [Odd-prime constructions and obstruction](../PrimeFactors/QuarticOddLocalPoints.lean) · [Combination over composite moduli](../PrimeFactors/QuarticLocalClassification.lean)

## Four small products

| Product | Prime factors | Remainder modulo 16 | Outcome |
| ---: | --- | ---: | --- |
| 2,501 | 41 × 61 | 5 | Passes every modulus and has the integer representation $1^4+4\cdot5^4$. |
| 2,773 | 47 × 59 | 5 | Fails modulo 47 because both numerator coordinates would vanish. |
| 2,173 | 41 × 53 | 13 | Fails modulo 16 even though both primes are 1 modulo 4. |
| 2,257 | 37 × 61 | 1 | Passes every modulus. No pair of ordinary integers gives $x^4+4y^4=2257$. |

The last example distinguishes satisfying all these modular tests from finding the coordinates at denominator one. Other rational denominators for 2,257 remain a separate question. In a plain consecutive Fermat scan, 48 fails and $49^2-2257=12^2$ gives the two primes. The benchmark driver finds 37 in its small-prime prepass and uses zero Fermat tests. [Checked examples](../PrimeFactors/QuarticLocalClassification.lean) · [Benchmark fixture](../benchmarks/cases.json)

## What can be checked from the product alone?

For every odd $N$, a single modulus $16N$ captures the complete criterion. Equivalently, once the test at 16 passes, the remaining question is whether $-1$ has a square root modulo $N$. [Exact equivalences and why the multiplier is sharp](one-modulus-and-the-low-bits-of-the-prime-sum.md)

Read the last four bits. Unless they represent 1 or 5, every positive denominator can be skipped for these quartic formulas. The screened program returns exactly the same pair or failure as the previous 2,048 trials on every eligible input. If the last four bits pass, **every modulus coprime to $N$ passes**. In fact a positive modulus $m$ fails precisely when $\gcd(m,N)$ has a prime divisor equal to 3 modulo 4. If someone supplies a failing $m<N$, taking its gcd with $N$ already gives a proper factor. [Executable last-bit check](../PrimeFactors/QuarticPublicResidueGate.lean) · [Single-modulus criterion and gcd theorem](../PrimeFactors/QuarticSingleModulus.lean)

Among the 64 ordered pairs of invertible remainders modulo 16, sixteen pass the product-only check and eight pass the complete criterion. On the actual full-size prime-pair population, the product-only share is within $1/4160$ of one quarter, and the complete share is within $1/8320$ of one eighth. These bounds use a published unconditional prime-count estimate. The last-bit check brings the average number of scheduled denominator trials below **0.751**, even charging all three trials on every allowed input. [Residue counts and transfer](../PrimeFactors/QuarticLocalPopulation.lean) · [Work bound](../PrimeFactors/QuarticLocalSearchWork.lean) · [Bennett, Martin, O’Bryant and Rechnitzer, Theorem 1.3](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5)

The Dirichlet-GRH estimate sharpens both absolute errors to at most $2^{-146}$. Lean checks the arithmetic transfer from both published endpoint estimates. The analytic estimates themselves are explicit hypotheses in this repository. [Population proof](../PrimeFactors/QuarticLocalPopulation.lean) · [Ernvall-Hytönen and Palojärvi, Corollary 2](https://arxiv.org/pdf/2003.01925#page=2) · [Independent verification of the Dirichlet-GRH result](https://math.mit.edu/~drew/shortgrh/)
