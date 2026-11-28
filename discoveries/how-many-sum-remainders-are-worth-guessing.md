# How many sum remainders are worth guessing?

Suppose the product of two unknown numbers leaves remainder 1 modulo 27. There are 18 possible ordered pairs of factor remainders. For each first remainder coprime to 27, its inverse is the only possible partner. Four sums occur. If we give the 18 pairs equal weight, two guesses cover twelve of them.

| Sum remainder | 2 | 11 | 16 | 25 |
| --- | ---: | ---: | ---: | ---: |
| Ordered pairs | 3 | 6 | 6 | 3 |

At modulus 9, the sums 2 and −2 are the most frequent. At modulus 27, the sums 2 and −2 each have half the weight of 11 or 16. Carrying an earlier ranking forward unchanged can therefore give a worse guess. [Prime-square weights](../PrimeFactors/PrimeSquareSumWeights.lean) · [Cube weights and complete table](../PrimeFactors/PrimeCubeSumWeights.lean)

## What two independent moduli buy

Fix a product of 1 modulo both 25 and 49. The Chinese remainder theorem gives one sum remainder modulo 1,225 for each pair of local sum remainders. The numbers of factor pairs multiply. The 840 ordered pairs produce 112 possible sums, with the following frequencies. [Product rule for coprime moduli](../PrimeFactors/CombinedSumWeights.lean)

| Ordered factor pairs yielding each sum | Number of sum remainders | Pairs covered |
| ---: | ---: | ---: |
| 35 | 4 | 140 |
| 14 | 10 | 140 |
| 10 | 28 | 280 |
| 4 | 70 | 280 |

Guessing each remainder once in descending order of frequency takes **37⅓ guesses on average**, compared with 56½ in a uniformly random order. That saves 115/339, or about **33.9%**, and Lean proves that no ordering has a smaller mean under this distribution. For example, the deliberately chosen primes 1,049 and 1,399 give product 1,467,551 and sum 2,448. Its remainder 1,223 is one of the four most frequent classes. Several exact sums can have the same remainder. Finding which one belongs to an input requires additional work. [Optimal order and worked product](../PrimeFactors/CombinedSumWeights.lean)

## How much information survives at higher powers?

For an odd prime $p$, fix $N$ coprime to $p$ and square modulo $p$. Give all ordered residue pairs with product $N$ modulo $p^e$ equal weight. Pick one pair and compute its sum. The average number of pairs sharing that sum is exactly $2e-2/(p-1)$. This grows only linearly with the exponent, even though the population of pairs grows exponentially. For $N=1$ modulo 125, the 100 pairs give 550 matches across 10,000 independent draws of two pairs. Two independently sampled sums agree 5.5% of the time. [Weights for every prime power](../PrimeFactors/PrimePowerPairWeight.lean) · [General formula and 125 example](../PrimeFactors/PrimePowerSumCollisions.lean)

A sharper question is how many different guesses are needed if we only want to cover half the pairs. At modulus $5^{100}$ with product remainder 1, the **exact minimum is $(5^{99}+7)/6$**, more than $2^{227}$ distinct remainders. There is a list of precisely this size. It consists of every attainable sum $s$ for which $s^2-4N$ is divisible by five. Omitting entries in favor of other guesses cannot give half coverage on a smaller list. The underlying counting theorem works at every exponent of five from two onward. [Exact minimum and attaining list](../PrimeFactors/HalfMassFive.lean) · [Bounds for other prime powers](../PrimeFactors/LocalSumGuessCoverage.lean)

These percentages describe a finite sample of **factor remainders**. The frequency among actual prime products also depends on which primes occur in each class. The project has established a separate full-size prime-population estimate at modulus 25. The coordinate sums themselves are classical objects studied as sumsets of modular hyperbolas. [Full-size prime counts](which-sum-remainders-come-up-most-often.md#what-about-all-eligible-2048-bit-products) · [Bower, Evans, Luo and Miller, *Coordinate sum and difference sets of d-dimensional modular hyperbolas*](https://arxiv.org/abs/1212.2930)
