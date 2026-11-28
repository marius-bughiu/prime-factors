# One modulus captures all the quartic tests

For every odd positive $N$, the cleared quartic congruence passes **every positive modulus** exactly when it passes **$16N$**. Both statements ask whether suitable locally primitive numerator coordinates and a positive denominator exist. The single-modulus theorem replaces an infinite list of questions with one whose input is known. Finding a witness, or deciding whether there is one efficiently, remains a computational question. [Equivalence for every odd input](../PrimeFactors/QuarticUniversalModulus.lean)

The multiplier is sharp. A fixed positive $c$ makes the test at $cN$ sufficient for every odd $N$ if and only if $16\mid c$. The product $2173=41\times53$ distinguishes all the other multipliers at once. It passes a positive modulus $m$ precisely when $16$ does not divide $m$. For example $8N$ passes and $16N$ fails. [Minimality and counterexample](../PrimeFactors/QuarticUniversalModulus.lean)

## An equivalent question stated using only the original input

First check that $N\bmod16$ is 1 or 5. If it is, the remaining question is simply whether **$-1$ has a square root modulo $N$**. In other words, does $N$ divide $u^2+1$ for some integer $u$? The equivalence holds for all positive odd inputs, including repeated prime factors. It follows by analyzing the prime powers dividing $N$ and applying the Chinese remainder theorem. A fast factor-free method for deciding the remaining square test on arbitrary balanced inputs is still open here. [Square criterion and worked witnesses](../PrimeFactors/QuarticLocalSquareCriterion.lean)

| $N$ | $N\bmod16$ | Square-root test |
| ---: | ---: | --- |
| 2,257 | 1 | $438^2+1=85N$, so both tests pass. There is no ordinary integer quartic representation at denominator one. |
| 2,173 | 13 | $401^2+1=74N$. The test at 16 still rejects it. |
| 2,773 | 5 | Its prime divisor 47 is 3 modulo 4, ruling out a square root of $-1$. |

These cases separate the cheap check on the last four bits from the square-root question on the full input. [Checked examples](../PrimeFactors/QuarticLocalSquareCriterion.lean) · [Integer representation check](../PrimeFactors/QuarticLocalClassification.lean)

## What would the answer tell us about the factors?

Suppose $N=pq$ is an odd semiprime and $N\bmod16$ is 1 or 5. Write $S=p+q$. The answer to the complete local test selects the sign in the sum congruence.

| Answer | Consequence for $S$ |
| --- | --- |
| Pass | $S\equiv N+1\pmod{16}$ |
| Fail | $S\equiv-(N+1)\pmod{16}$ |

The reason is elementary. In the first case both primes are 1 modulo 4, so $16\mid(p-1)(q-1)$. In the second both are 3 modulo 4, so $16\mid(p+1)(q+1)$. When $N\bmod16=5$, the signed congruences hold modulo **32**. The product alone leaves two possible remainders for $S$; the supplied answer chooses between them. Every higher-precision sum in the selected class still admits a modular pair with that factor sign at every power of two. For $N\bmod16=1$ both lifts of the selected remainder modulo 32 can occur; higher powers may impose further restrictions there. [Prime-sum equivalences and permitted modular pairs](../PrimeFactors/QuarticLocalSumBits.lean)

Two selected 32-bit inputs differ in just one binary digit. In hexadecimal they are `AB4EBCC5` and `AF4EBCC5`. Both have remainder 5 modulo 32.

| Product | Certified prime factors | Answer | Sum modulo 32 |
| ---: | --- | --- | ---: |
| 2,874,064,069 | 48,541 × 59,209 | Pass | 6 |
| 2,941,172,933 | 48,487 × 60,659 | Fail | 26 |

The products share their lowest 26 bits and agree in 31 of 32 positions. This example shows that a single changed input bit can switch the selected sum remainder. [Certified examples](../PrimeFactors/QuarticLocalSumBits.lean) · [Independent Fermat replays](../benchmarks/cases.json)

## Could the low product bits predict the answer at full size?

Fix **any particular string of 160 low product bits** that ends in `0001` or `0101`. Among eligible 2,048-bit prime products with exactly those bits, the proportion passing the complete local tests differs from **one half** by at most $2^{-147}$ under the stated Dirichlet-GRH prime-count estimates. Each such subpopulation is nonempty. This estimate is conditional on the individual string, so seeing which string occurred offers almost no help in choosing the sign. [Conditional estimate for each 160-bit suffix](../PrimeFactors/QuarticLocalConditionalBits.lean)

The equal split is exact for the allowed pairs of factor remainders. Replacing $(a,b)$ by $(-a,-b)$ preserves $ab$ and interchanges the two factor classes modulo 4. The argument then bounds the number of actual prime products in these paired remainder classes using the published estimates. It compares classes with the **same fixed product remainder** throughout. [Finite symmetry and population transfer](../PrimeFactors/QuarticLocalConditionalBits.lean) · [Ernvall-Hytönen and Palojärvi, Corollary 2](https://arxiv.org/pdf/2003.01925#page=2)

## If the answer were free, how far would the search still have to go?

For any positive modulus divisible by 16, including one with large odd factors, either sign retains **exactly half the distinct admissible sum remainders in a complete period**. Negation pairs each sum with its opposite, interchanging the two disjoint sign classes. A short search interval can contain unequal numbers from the two halves. [Exact half-count for distinct sums](../PrimeFactors/QuarticHalfSumResidues.lean)

For $N\equiv5\pmod{16}$, consider testing sums in increasing order from $\lceil2\sqrt N\rceil$. Give the search the correct sign and all the precision it wants at the prime two. The exact number of **wrong sums before the true sum** that survive is

$$\left\lfloor\frac{p+q-\lceil2\sqrt N\rceil}{32}\right\rfloor.$$

Each survivor has modular witnesses at every power of two, and each fails the integer square test. For the two 32-bit examples above there are 16 and 21 earlier survivors, respectively. At full size, the inputs that both have $N\equiv5\pmod{16}$ and have fewer than $2^{895}$ earlier survivors make up less than one in $2^{35}$ of the entire eligible prime-pair population. This count concerns the ordinary ascending scan with these tests. [Exact count, examples and population theorem](../PrimeFactors/QuarticSignedSumPrefix.lean)
