# What many prime squares buy a remainder guess

If two unknown factors multiply to 1 modulo some modulus, how many guesses does it take to name their **sum remainder**? Give each possible ordered pair of factor remainders equal weight. A guess counts once, and the correct guess counts too. A guess of a remainder can identify a whole group of possible sums. Finding which integer in that group is the true sum is a separate problem.

For modulus **7,239,457,225**, there are **41,767,264** possible sum remainders. Guessing them in a uniformly random order takes **20,883,632.5** guesses on average. The best order takes **470,695,147/48**, about **9.81 million**, a **53.04% saving**. The modulus is the product of the squares of 5, 7, 11, 13 and 17. Lean checks the optimum on the actual sum remainders modulo that one number. [Exact minimum, support and rank mass](../PrimeFactors/FiveSquareGuessRanks.lean)

| Prime squares used | Possible sum remainders | Ordered factor pairs | Best mean guesses | Random-order mean |
| --- | ---: | ---: | ---: | ---: |
| 5² | 7 | 20 | 13/4 | 4 |
| 5², 7² | 112 | 840 | 112/3 | 113/2 |
| Add 11² | 5,152 | 92,400 | 44,521/30 | 5,153/2 |
| Add 13² | 345,184 | 14,414,400 | 1,331,266/15 | 345,185/2 |
| Add 17² | 41,767,264 | 3,920,716,800 | 470,695,147/48 | 41,767,265/2 |

For the first three rows we also enumerated every possible first factor remainder and its inverse and counted the sums directly. For five squares there are only 32 groups to count by frequency. A real semiprime can share the stated product remainder. We deliberately selected $139{,}649{,}129{,}870{,}251=11{,}809{,}331\times11{,}825{,}321$ with that property and close factors. Its Fermat benchmark takes three midpoints and checks the factorization in Lean. This particular input supplies no estimate of the probability of a sum for actual prime products. [Reproduce the counts](../experiments/joint_sum_guess_counts.py) · [Small benchmark fixture](../benchmarks/cases.json)

## Can the relative saving keep growing?

Yes in this model. **For every positive fraction, there is a modulus for which the mean number of guesses is below that fraction of the random-order mean.** The witness modulus uses distinct prime squares and the fixed product remainder 1. Both the number of labels and the number of required guesses can grow. [Statement on actual modular sum labels](../PrimeFactors/ArbitrarilyBiasedSumGuesses.lean)

The reason can be seen one prime at a time. At each odd prime square $p^2$, there are two particularly frequent sums with $p$ ordered pairs each. Every other attainable sum has just two. The Chinese remainder theorem makes the joint multiplicities multiply. Guessing in descending order of these weights minimizes the mean. [Local weights and their effect](../PrimeFactors/PrimeSquareGuessAffinity.lean) · [Transferring the weights to one modulus](../PrimeFactors/CoprimeGuessTables.lean)

For a table with $A$ labels and normalized probabilities $P_s$, put $F=(\sum_s\sqrt{P_s})^2/A$. A uniform table has $F=1$. For independent tables the values of $F$ multiply. A classical guesswork inequality says that twice the optimal mean is at most $1+AF$. Lean checks the finite version used here. For every prime $p\ge11$, our local $F$ is at most $1-1/(2p)$. The sum of reciprocal primes diverges, so multiplying enough of these local factors makes their product arbitrarily small. The deduction uses unconditional elementary number theory formalized in Mathlib. [Finite probability inequality](../PrimeFactors/IndependentGuessRanks.lean) · [Sason and Verdú, Theorem 5(a), equation 73](https://arxiv.org/pdf/1801.01265) · [Product bound](../PrimeFactors/PrimeGuessProducts.lean)

The conclusion also holds for **every fixed positive integer $n$**, even when the selected primes must exceed a given cutoff. Prime numbers congruent to 1 modulo $8n$ make $n$ a nonzero square. Their reciprocals have divergent sum, so a finite selection can again make the relative mean as small as desired. Lean proves this using quadratic reciprocity and Mathlib’s theorem on primes in arithmetic progressions. These primes can be larger than $n$. The experiment being predicted still draws a random ordered *residue pair* with product congruent to $n$. [Unconditional supply of splitting primes](../PrimeFactors/SplittingGuessPrimes.lean) · [Result for any fixed positive product](../PrimeFactors/FixedProductSumGuesses.lean)

## What remains expensive?

For distinct prime squares and a fixed unit product that is square at every prime $p$, define $H=\prod_p(p-1)$. No single sum label has probability above $1/H$. Even the best list needs at least $\lceil H/2\rceil$ labels to cover half the pairs. Every possible order has mean rank at least $(H+1)/2$. For the five primes above, $H=46{,}080$, so even half coverage takes at least 23,040 labels. As more primes enter the modulus, this absolute lower bound increases. The apparent improvement against random order reflects how quickly that comparison grows. [Absolute bounds for lists and guessing orders](../PrimeFactors/JointSumGuessFloor.lean)

The model takes a random pair of factor **remainders** as its sample. These results supply neither the true remainder of a given semiprime nor an inexpensive test for a proposed remainder. For actual 2,048-bit prime products the project has a separate guarantee on how many exact square tests an elementary search saves, and a lower bound on the work it still has to do. [Full-size search and remaining work](using-both-the-location-and-remainder-of-a-sum.md#how-much-work-is-still-unavoidable)
