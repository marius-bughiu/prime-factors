# The product rules out quartic denominators before any roots are taken

The three candidate denominators lie in separate intervals for the ratio of the prime factors. The product itself can rule out one or two of them. The resulting executable returns the same prime pair or failure as the full list of 2,048 denominator trials on **every** 2,048-bit product of two distinct 1,024-bit primes. [Equality with the reference search](../PrimeFactors/ProductSelectedQuarticDenominators.lean)

Write $B=2^{1024}$. The public list is determined by two integer comparisons.

| Product interval | Denominators to try |
| --- | --- |
| $9N<5B^2$ | 1, 725, 1,517 |
| $5B^2\le9N$ and $3N<2B^2$ | 1, 1,517 |
| $2B^2\le3N$ | 1 |

Over the uniform population of eligible prime pairs, the list has **fewer than 1.90 entries on average**, a saving of more than 36⅔% against three scheduled trials. Both lists are charged in full before any early return. The estimate counts how many prime pairs lie in rectangles on a 256-division grid. It uses a published unconditional prime-count bound at modulus five as an explicit input to Lean. [Population proof and its hypothesis](../PrimeFactors/QuarticGatePopulation.lean) · [Bennett, Martin, O’Bryant and Rechnitzer, Theorem 1.3](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5)

For a primitive representation, the two Sophie Germain factors of the scaled number satisfy $256A_{\rm large}\le257A_{\rm small}$ throughout the full-size recognition intervals. The denominator divides between them in fourth powers. When $p<q$, a primitive denominator of 1 forces $256q\le257p$. Denominator 725 forces $9p<5q$, and 1,517 forces $3p<2q$ and $8q<13p$. These ratio ranges are disjoint. Because $q<B$, multiplying the necessary inequalities by $q$ gives the two public product tests. [Factor bounds, disjointness and reduction of nonprimitive points](../PrimeFactors/QuarticDenominatorBands.lean)

One input can pass several raw trials if its coordinates are rescaled versions of the same primitive point. The uniqueness result concerns the denominator *after cancellation*. The two deliberately chosen full-width examples both pass all three raw trials in the fixed list. In each case the first one already returns the prime factors. [Examples and prime certificates](a-full-size-quartic-example.md) · [Denominator cancellation](../PrimeFactors/ReduceQuarticDenominator.lean)
