# How often the first even sums work

If two odd primes are close, their average is close to the square root of their product. Given only the product $N$, the first guess for their sum is therefore $2\lceil\sqrt N\rceil$. Subsequent guesses add two each time. When a guess is correct, half of it is the primes’ average $m$, and $m^2-N$ is the square of their half-difference. Adding and subtracting that half-difference gives the factors.

How often must this familiar search succeed? Count each pair of distinct 1024-bit primes whose product has 2048 bits once, with the smaller prime first. Lean proves the following lower bounds over that entire finite population. [Population proof](../PrimeFactors/FirstSumMenuPopulation.lean) · [Definition of the eligible pairs](../PrimeFactors/MixedPrefixSample.lean)

| Number of even sums tried | Fraction of eligible products that must be found |
| ---: | ---: |
| 1 | Greater than $2^{-517}$ |
| $2^{168}$ | Greater than $2^{-433}$ |
| $2^{552}$ | Greater than $2^{-241}$ |

The first row means that the single guess succeeds somewhere in a provably large population of close pairs. Its guarantee is too small to promise success for a particular input. The other two rows allow up to $2^{168}$ or $2^{552}$ square tests after computing the initial square root.

## Counting close pairs

Set $X=2^{1023}$. Primes between $283X/200$ and $2X$ automatically give a 2048-bit product when multiplied together. Divide the interval $[X,2X)$ into $b$ buckets of width $D$. Two upper-band primes in one bucket differ by less than $D$. If $D^2\le 8XJ$, their true sum appears among the first $J$ guesses. [Distance bound](../PrimeFactors/FirstSumMenuPopulation.lean)

Let $H$ be the number of upper-band primes. If the bucket counts are $h_i$, Cauchy’s inequality gives $\sum_i h_i^2\ge H^2/b$. The sum counts ordered pairs within buckets. Removing the $H$ pairs with equal primes and dividing by two counts the distinct pairs once. Bounds on the total prime counts then give the three frequencies above. This calculation works even when some buckets are empty. [Upper-band prime count](../PrimeFactors/ChebyshevPrimeSample.lean) · [All-band prime count](../PrimeFactors/SquareRootPhasePopulation.lean)

A list of $2^{168}$ guesses also splits into $2^{128}$ blocks of $2^{40}$ guesses. With a message selecting a successful block, the search needs at most $2^{40}$ square tests for each covered product. For $2^{552}$ guesses the corresponding message has 512 bits. The proof counts products for which such a message exists. It gives no method for finding a successful block from the product more cheaply than testing the blocks. [Block equivalence](../PrimeFactors/FirstSumMenuPopulation.lean)
