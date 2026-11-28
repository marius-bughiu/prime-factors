# When one public square root predicts the prime sum

For 601,049, a square root computed from the product predicts the true prime sum, 1,590. For 842,713, the same calculation predicts 1,590 again and misses. The products agree on their lowest twelve bits. The difference is in the prime gaps. At the width used here, the guess succeeds exactly when the gap is divisible by 32 with an odd quotient. [Checked inputs and results](../PrimeFactors/ShiftedSquareSumReadout.lean)

This asks a different question from how many factor bits a **supplied true sum** determines. Here the only inputs are the product and the promised factor width. At full size they yield one whole sum to check, and fewer than **one in $2^{500}$** eligible products pass. This coverage bound is unconditional. [Coverage proof](../PrimeFactors/ShiftedSquareSumCoverage.lean) · [What supplied sum bits determine](how-many-sum-bits-identify-the-factor-endings.md)

## Two ten-bit prime pairs, one prediction

Ten-bit primes have a sum in $[1024,2048)$. For both products the calculation gives the opposite remainders 458 and 1,590 modulo 2,048. Only 1,590 is in the sum interval. The prime labels below verify the reading after the prediction. [Reproducible fixture](../benchmarks/shifted-square-sum-readout.json) · [Prime certificates](../PrimeFactors/FactorEndingSeparationControls.lean)

| Public product | Certified primes | Actual sum | Prime gap | Result of checking 1,590 |
| ---: | --- | ---: | --- | --- |
| 601,049 | 619 × 971 | 1,590 | 352 = 32 × 11 | $1590^2-4N=352^2$ |
| 842,713 | 827 × 1,019 | 1,846 | 192 = 64 × 3 | $1590^2-4N$ is negative |

Each run takes eight modular root-lifting steps and checks one integer sum. On a hit, the sum and the square root of its discriminant give the two factors. On the miss, the full input remains unresolved. The two chosen examples illustrate the exact condition. [Bounded experiment](../experiments/shifted_square_sum_readout.py) · [Soundness and completeness in the promised interval](../PrimeFactors/ShiftedSquareSumReadout.lean)

## Why these two sum remainders are the best modular guesses

Fix an odd number of bits $e=2j+3$ with $j\ge2$, and a product remainder $N\equiv1\pmod8$. For the modular count, give each odd first-factor remainder modulo $2^e$ equal weight. Its unique partner is determined by the product. Exactly **two** sum remainders tie for the largest number of ordered pairs. The two are opposites. A square root $r$ of $N+2^{2j}$ modulo $2^e$ gives them as $2r$ and $-2r$. [Count of maximizing sums](../PrimeFactors/DyadicSumPeak.lean) · [Public root and its two readings](../PrimeFactors/OddWidthSumPredictions.lean)

Write $h=(p+q)/2$ and $d=(q-p)/2$. The identity $h^2-N=d^2$ explains the shift. One of the predictions is true precisely when $q-p$ equals $2^{j+1}$ times an odd integer. Since a nonzero gap has only one exact power of two, the same prime pair can meet this condition at **at most one** of these odd widths. When a prediction is correct, the observed product and sum remainders determine exactly $j+2=(e+1)/2$ low bits of each factor, up to swapping. At the next factor bit another modular pair is compatible. [Proofs of the gap condition, disjointness and factor precision](../PrimeFactors/OddWidthSumPredictions.lean)

For example, product remainder 1 modulo 128 has 64 ordered factor pairs. Sums 46 and 82 are the most frequent, at 16 pairs each. A correct guess of either identifies four low factor bits. The only sum readings that identify five bits are 62 and 66, each occurring on eight pairs. [Complete 64-pair count and precision checks](../PrimeFactors/DecidableSumGuessMass.lean)

## Predicting 161 low sum bits on full-size prime pairs

Fix **one** 161-bit product remainder ending in binary `001`. A predictor seeing only this remainder makes the same single guess for every product in the class. In the uniform modular count each of the two best guesses covers $2^{81}$ of $2^{160}$ ordered pairs, giving an exact success fraction of $2^{-79}$. Even on a hit, those 161 observed bits determine **81 low bits of each factor**. [Maximum modular weight](../PrimeFactors/DyadicSumPeak.lean) · [Precision at a winning sum](../PrimeFactors/OddWidthSumPredictions.lean)

Now count actual unordered pairs of distinct 1,024-bit primes whose 2,048-bit product has that specified remainder. The best single-guess success fraction is within **$2^{-225}$ of $2^{-79}$**, assuming the prime-count estimates of Ernvall-Hytönen and Palojärvi under Dirichlet GRH. Lean takes their endpoint estimates as inputs. Every actual maximizing sum is one of the two modular winners. Their actual prime-pair counts can differ. A predictor reading additional product digits has more information than this comparison allows. [Full-size conditional optimum](../PrimeFactors/FullWidthSumPrediction.lean) · [Transfer for each guess](../PrimeFactors/DyadicSumGuessPopulation.lean) · [Ernvall-Hytönen and Palojärvi, Corollary 2](https://arxiv.org/pdf/2003.01925#page=2)

For the other odd product endings the chance of a correct 161-bit sum guess is smaller. If the product is 3 or 7 modulo 8, the best share is within $2^{-304}$ of $2^{-158}$. For 5 modulo 8 it is within $2^{-303}$ of $2^{-157}$. The same prime-count estimate applies separately in each fixed 161-bit product class. Every attainable sum in those local models has exactly four or eight ordered presentations respectively. [All three fixed-suffix estimates](../PrimeFactors/FullWidthSumPrediction.lean) · [Ordered-pair counts](../PrimeFactors/DyadicSumPeak.lean)

## Predicting the whole sum at 1,025 bits

For two 1,024-bit primes, the sum lies in $[2^{1024},2^{1025})$. At $e=1025$, exactly one of the two opposite predictions is in this interval. For products equal to 1 modulo 8, it is the true integer sum exactly when $q-p$ is divisible by $2^{512}$ with an odd quotient. The test returns no pair outside that product class. [Whole-sum criterion](../PrimeFactors/ShiftedSquareSumReadout.lean)

The denominator for the **$2^{-500}$ upper bound** includes *all* unordered pairs of distinct 1,024-bit primes with 2,048-bit product. To bound the numerator, fix the first prime. The exact gap condition puts the second prime in a single class modulo $2^{513}$. Counting positions in that class and excluding multiples of 3, 5, 7, 11 and 13 gives an upper count. The proof counts both orderings and uses a lower bound on the total prime-pair population. It needs no hypothesis on the distribution of primes in these large residue classes. [Unconditional coverage proof](../PrimeFactors/ShiftedSquareSumCoverage.lean) · [Unconditional population bound](../PrimeFactors/ChebyshevPrimeSample.lean)

One deliberately constructed full-size comparison passes the product condition modulo 8. Its certified primes have a gap with **540** trailing zero bits. The 1,025-bit prediction requires exactly **512**, so the check returns no factors. This example shows why testing only for divisibility by $2^{512}$ would overcount the successes. [Full-size negative control](../PrimeFactors/ShiftedSquareSumFullSize.lean)
