# Why a larger product can have a smaller prime sum

$85=5\cdot17$ has prime sum 22. The slightly larger number $91=7\cdot13$ has prime sum 20. Requiring the primes to have the same bit length still allows a whole sequence of reversals. Every prime in this table has eight bits, and every product has sixteen.

| Product | Primes | Sum |
| ---: | --- | ---: |
| 32,881 | 131 and 251 | 382 |
| 33,017 | 137 and 241 | 378 |
| 33,823 | 149 and 227 | 376 |
| 34,393 | 163 and 211 | 374 |
| 34,427 | 173 and 199 | 372 |

A predictor that always holds its value or increases as the product grows can get at most one row right. How often could the best such rule work at full size? [Lean check of all five rows](../PrimeFactors/PrimeSumOrderReversals.lean)

## How often one nondecreasing prediction agrees

Count each pair of distinct 1,024-bit primes $p<q$ with a 2,048-bit product $N=pq$ once. Let $g(N)$ be any nonnegative integer prediction of $p+q$ that never decreases as $N$ increases. The bounds apply even if $g$ uses unlimited computation. Each fraction below uses the population named in its row. [Full-population proof](../PrimeFactors/MonotoneSumPopulation.lean) · [Proof for separated primes](../PrimeFactors/SeparatedMonotonePopulation.lean)

| Population | Fraction with the exact sum | Fraction within $2^{128}$ of the sum |
| --- | ---: | ---: |
| All eligible products | $<2^{-484}$ | $<2^{-419}$ |
| Products with $q-p\ge 2^{1006}$ | $<2^{-979}$ | $<2^{-850}$ |

**More than two thirds** of all eligible products meet the gap condition in the second row. To bound the excluded population, fix the smaller prime. Each possible gap below $2^{1006}$ specifies at most one larger prime. The proof compares this upper count with an unconditional lower bound on the number of eligible pairs. [Gap count and population comparison](../PrimeFactors/SeparatedMonotonePopulation.lean) · [Prime-pair population bound](../PrimeFactors/ChebyshevPrimeSample.lean)

## How long can the sum keep falling?

The five-row pattern occurs on a much larger scale. Among the products with gap at least $2^{1006}$, there exists a sequence of **more than $2^{979}$** strictly increasing products whose prime sums strictly decrease. The proof establishes existence without listing them. [Full-size sequence theorem](../PrimeFactors/PrimeSumOrderReversals.lean)

Suppose every such sequence had length at most $L=2^{979}$. Group each product by the length of the longest decreasing-sum sequence starting there. Two products in one group cannot form a reversal, since the earlier one could be placed in front of the later one's sequence. The sums within each group therefore agree with a nondecreasing predictor. Each predictor covers strictly less than $1/L$ of this population, so $L$ groups cannot cover it all. [Grouping argument](../PrimeFactors/DecreasingSumChains.lean) · [Extension to a predictor](../PrimeFactors/MonotoneSumExtension.lean)

## Why the counts are small

Divide the product range into blocks of width $W$. Within one block, the prediction stays between its values at the two endpoints. With allowed error $E$, the true sum can extend at most $E$ farther in either direction. Across all blocks the increases in $g$ add up to its total rise. Every eligible sum is below $2^{1025}$, so capping the predictor at $2^{1025}-1$ bounds this rise while preserving every hit. [Block-count proof](../PrimeFactors/MonotoneSumBlocks.lean) · [Clipping argument](../PrimeFactors/MonotoneSumPopulation.lean)

Now fix a sum $S$ within one block. A candidate smaller factor $x$ gives product $x(S-x)$. At most $\lfloor\sqrt W\rfloor+1$ sorted pairs with that sum fit in the block. If both pairs have prime gap at least $W$, their different products are at least $W$ apart. A block then holds at most one pair per sum. Taking $W=2^{1006}$ gives the stronger second row. [Fixed-sum spacing](../PrimeFactors/FactorSumProductCell.lean) · [One-pair bound](../PrimeFactors/SeparatedMonotonePopulation.lean)

## What can a square-root guess achieve?

Fermat's first midpoint suggests the sum $2\lceil\sqrt N\rceil$. The identity $(p+q)^2-4N=(q-p)^2$ explains why this can work when the primes are close. Across the full population this single guess is exactly right on **more than $2^{-516}$** of the products and comes within $2^{128}$ on **more than $2^{-452}$**. The first row of the table gives the corresponding upper bounds. Fermat's search can also test subsequent midpoints. [Lower bounds for the first guess](../PrimeFactors/MonotoneClosePrimeLower.lean) · [Fermat search](../PrimeFactors/Fermat.lean)

A predictor that only decreases or holds steady has an exact success fraction below $2^{-1007}$ across the full population. Fix the smaller prime $p$ and increase its partner $q$. The true sum $p+q$ increases while the predicted sum cannot increase, so at most one partner can give equality. Earlier polynomial results constrain the degree of a relation between $N$ and $p+q$. The bounds here use only the direction in which a prediction moves. [Nonincreasing predictors](../PrimeFactors/AntitoneSumPopulation.lean) · [Polynomial limits](how-often-can-a-polynomial-describe-the-prime-sum.md)

## What if we divide two polynomials and round down?

Fix polynomials $A$ and $B$, each of degree at most $2^{28}$, and predict the sum by $\lfloor A(N)/B(N)\rfloor$. Over all eligible prime pairs, this signed integer prediction is exactly right on **fewer than one in $2^{453}$** and comes within $2^{128}$ on **fewer than one in $2^{388}$**. The bounds allow arbitrary real coefficients of any magnitude and impose no size limit on nonzero denominator values. Every input with $B(N)=0$ counts as a miss, including a shared zero of $A$ and $B$. [Signed-floor population bounds](../PrimeFactors/RoundedRationalSumPopulation.lean)

The denominator zeros separate the poles and any removable gaps. Between them, the quotient can change direction only at a zero of $A'B-AB'$. If this polynomial vanishes identically, the quotient is constant on each interval where it is defined. For degrees at most $d$, keeping the cut points as separate pieces gives at most $6d+1$ pieces. Rounding down preserves the direction on each piece. The earlier polynomial identity bound counted exact zeros of a relation $F(N,p+q)=0$. Here a hit can occur anywhere inside a rounding interval, with the additional tolerance allowed around the resulting integer. [Interval proof](../PrimeFactors/RationalPredictionTurns.lean) · [Bounds across pieces](../PrimeFactors/PiecewiseMonotoneSumPopulation.lean) · [Earlier polynomial identities](how-often-can-a-polynomial-describe-the-prime-sum.md)
