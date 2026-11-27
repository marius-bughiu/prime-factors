# How accurately would we need the interval total?

Suppose we are given a 2,048-bit product $N$ of two distinct 1,024-bit primes and an estimate of its signed character total $V$. An error of at most $2^{1045}$ leaves at most **1,048,576 candidate sums**. An error of at most $2^{1025}$ already determines the exact sum. The estimate has to come from somewhere. Our proofs specify how much information it would supply, and which simple ways of estimating it fail. [What the total measures](can-short-character-averages-reveal-the-primes.md#one-longer-sum-that-does-determine-the-answer) · [Candidate-count proof](../PrimeFactors/PrimitiveIntervalCandidateBand.lean)

## A less accurate estimate still narrows the search

Put $B=\lfloor\sqrt{N/2}\rfloor$ and let $S=p+q$. At this public length the signed total is $(S-B-1)^2-2N+2B+1$. Two candidate sums $s<t$ therefore predict totals separated by $(t-s)(t+s-2B-2)$. We know the true sum is at least $2B+2$ and has remainder $N+1$ modulo four. Distinct candidates differ by at least four. That spacing bounds how many predictions fit in an interval of uncertainty. [Proof of the spacing and finite count](../PrimeFactors/PrimitiveIntervalCandidateBand.lean)

| Maximum absolute error in the supplied integer | Most candidate sums that can survive at 2,048 bits |
| --- | ---: |
| $2^{1025}$ | 1 |
| $2^{1045}$ | $2^{20}=1,048,576$ |
| $2^{1057}$ | $2^{32}=4,294,967,296$ |

The candidates also have to lie between $2B+2$ and $4B+2$. For a product of distinct balanced odd primes, the true sum is always in the list if the stated error bound holds. An exact square discriminant identifies a genuine factorization. None of these counts assumes a way to produce the estimate. [Finite list and containment](../PrimeFactors/PrimitiveIntervalCandidateBand.lean)

## A deliberately noisy clue on the 39-bit example

We used the same two 20-bit primes as in the square-divisor experiment. Their product is 419,636,024,497. The disclosed factors give the exact total $-112{,}543{,}867{,}588$. We added 5,000,000 and supplied the resulting $-112{,}538{,}867{,}588$ to the sum test, with an error allowance of 16,000,000. This makes the source of the information explicit. [Original seeded prime pair](what-four-square-divisors-reveal.md#a-39-bit-example-with-supplied-clues)

Five sums survive the supplied reading and the known remainder modulo four. They are 1,310,538, **1,310,542**, 1,310,546, 1,310,550 and 1,310,554. Only the bold sum gives an integer-square discriminant. Its two primes are 556,559 and 753,983. [Checked total, five sums and factorization](../PrimeFactors/PrimitiveIntervalSuppliedExample.lean)

## What if the estimate is much coarser?

An estimate $v$ with absolute error as large as $2^{1450}$ still places the smaller prime within $2^{470}$ of an explicit real number on all but fewer than one in $2^{15}$ eligible pairs. This is a radius on the number line. The location depends on the supplied estimate for this particular product. The remaining interval is very large. [Pointwise root bound](../PrimeFactors/PrimitiveIntervalRootBand.lean) · [Population and numerical bound](../PrimeFactors/PrimitiveIntervalRootPopulation.lean)

First estimate the sum by $B+1+\sqrt{\max(0,v+2N-2B-1)}$, raising it to $2\sqrt N$ if it lies below that value. Call the result $t$. Then the estimated smaller factor is $x=(t-\sqrt{t^2-4N})/2$. The first square root controls the error in the sum. The second becomes sensitive when the two actual primes are close. If $y=t-x$, then $xy=N$ and $(x-p)(x-q)=x(t-S)$. Since $x\le\sqrt N\le S/2$, we have $q-x\ge(q-p)/2$. This bounds how much the smaller root moves. A direct count of integer pairs shows that the true gap is at least $2^{982}$ outside the stated exceptional fraction. [Proof with real-valued errors](../PrimeFactors/PrimitiveIntervalRootBand.lean) · [Counting the small gaps](../PrimeFactors/PrimitiveIntervalRootPopulation.lean)

## Does the average over one full period work?

A gcd is cheap to evaluate at a chosen index. One might hope its average over a complete period describes its behavior in the much shorter triangular interval used by $V$. Even granting the exact complete-period average, that substitution always decodes to a wrong sum at 2,048 bits. [Finite-period calculation and wrong-sum proof](../PrimeFactors/PrimitiveIntervalPeriodMean.lean)

For example, at $143=11\cdot13$, the weighted gcd sum over the triangle is 172. Substitution of the full-period gcd average predicts a signed total of $-15296/143$. Rounding that down gives $-107$ and decodes to 20. The actual signed total is $-44$ and decodes to 24. In general the full-period gcd average itself equals $(2p-1)(2q-1)/N$. Multiplying it by $N$ gives $4N-2(p+q)+1$, which determines the sum of the primes. [Lean calculation at 143](../PrimeFactors/PrimitiveIntervalPeriodMean.lean) · [Tóth’s weighted gcd identity](https://cs.uwaterloo.ca/journals/JIS/VOL14/Toth/toth9.pdf#page=2)

The paper by Kaltenböck, Kiuchi, Saad Eddin and Ueda estimates weighted gcd averages across moduli. Its RH refinement also assumes the zeta zeros are simple. The estimate required here concerns one specified modulus and one short triangular interval. The full-period failure above follows directly from finite arithmetic. [Published averaging range and hypotheses](https://link.springer.com/article/10.1007/s00025-021-01357-x#Sec1)

## Would a multiple of the product be accurate enough?

Choose any real coefficient $c$ before seeing the primes and predict $V=cN$. The chance of reaching the $4B$ decoding tolerance is less than $2^{-482}$ on a uniformly chosen eligible pair. Even a menu of $2^{64}$ fixed coefficients, with the best one selected separately for each product, succeeds on fewer than one in $2^{418}$ eligible pairs. At the much coarser error budget $2^{1450}$, a single coefficient still succeeds on fewer than one in $2^{269}$ pairs. [Fixed-coefficient and menu bounds](../PrimeFactors/PrimitiveIntervalShapePopulation.lean)

To see why the population matters, consider guessing a fixed ratio $r$ between the larger and smaller primes. This suggests the factor sum $(\sqrt r+1/\sqrt r)\sqrt N$. Any fixed $c$ which attains the decoding tolerance gives such a fixed ratio whose predicted sum is within eight of the truth on every success. For each smaller prime, that requirement places the larger prime in a narrow interval around $rp$. Counting those intervals gives the bounds above. They concern a constant multiple or a menu fixed in advance. A product-specific formula with a larger range of outputs would require its own analysis. [From a coefficient to a ratio](../PrimeFactors/PrimitiveIntervalShape.lean) · [Counting compatible prime pairs](../PrimeFactors/FixedRatioSumPopulation.lean)
