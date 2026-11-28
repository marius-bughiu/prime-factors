# How many bits would someone have to tell us?

**25 carefully chosen bits suffice, and 24 bits cannot match what knowing the true sum remainder buys.** The goal here is to guess either prime’s remainder modulo 7,239,457,225. The product remainder is public. Someone who already knows both integer primes may send one fixed-width message, and the guesser chooses a list using just the public remainder and that message. The comparison covers distinct 1,024-bit primes with a 2,048-bit product under the stated Dirichlet-GRH prime-count estimates. [Sharp threshold in Lean](../PrimeFactors/FactorAdviceThreshold.lean) · [How the full-width estimates enter](../PrimeFactors/FiveSquarePrimeSupply.lean)

| Information supplied | Mean number of guesses | What fits in 100 guesses? |
| --- | ---: | --- |
| Product remainder alone | 980,179,200.50 at best, rounded | — |
| Any message of at most 24 bits, fixed width | More than 58.9232 for every scheme | Fewer than 85.5824% of inputs for every scheme |
| True sum remainder | 48.899 at best, rounded | — |
| A particular truthful 25-bit message | Fewer than 31 with a suitable order | Every input fits in 59 guesses |

Each guess names one unordered pair of remainders compatible with the product. The counts give the position of the correct pair. Inferring the message from the integer product, recognizing that a guess is correct and recovering the primes are separate open costs. [Cost with the true sum](if-the-true-sum-remainder-were-given.md) · [Cost with the product alone](guessing-a-factor-remainder-instead-of-the-sum.md)

## Why even an all-knowing helper faces a limit

At each public product remainder, 3,920,716,800 different first-factor remainders are possible. One list entry covers at most two of them, one for each way to order the pair. If the helper may choose from B messages, the first t entries in all those lists together cover at most 2Bt first-factor remainders. The best possible mean in the uniform modular population is therefore at least T/(4B) + 1/2, where T is the number of possible first remainders. The prime-count estimates transfer this bound and the prefix count to the full-size population. The helper may even inspect both integer primes before picking the message. The lists themselves depend only on the public product remainder and the message. [Counting proof](../PrimeFactors/FactorOrbitAdviceFloor.lean) · [Full-size population and message selection](../PrimeFactors/FiveSquareAdviceLimits.lean)

## What the 25 bits say

Number the pairs in a public order starting at zero. A helper who knows the true pair finds its position and sends the remainder of that position upon division by 33,554,432. The receiver looks only at entries with this remainder. Even the longest list has at most 59 such entries. This construction specifies the information an outside source would have to provide. Computing or storing a full ordered list and supplying the message have no time allowance in this count. [Construction and worst-case bound](../PrimeFactors/FactorOrbitAdviceConstruction.lean) · [Equivalence to choosing among complete lists](../PrimeFactors/FactorOrbitAdviceMenu.lean)

For a smaller example, take the deliberately chosen primes 701 and 751. Their product is 526,451. Modulo 25 their product is 1, and their two remainders are both 1. Order all compatible unordered pairs by putting different-member pairs first and sorting numerically within the two groups. The pair (1, 1) is tenth, at zero-based position 9. With two bits the helper sends 01, since 9 divided by 4 leaves remainder 1. The receiver tests positions 1, 5 and 9 in that order. The target is third. The example uses the known primes to obtain the clue. Its separate integer certificate verifies the two primes and their product. [Reproduce the ordering](../experiments/complementary_factor_guesses.py) · [Certificate fixture](../benchmarks/cases.json)

If the helper only knows the sum remainder, preserving its best mean exactly at every modular product takes 27 bits. [What merging two sums costs](compressing-the-sum-remainder.md)
