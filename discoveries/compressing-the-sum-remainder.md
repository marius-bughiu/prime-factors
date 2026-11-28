# How short can a message about the sum be?

A helper who knows only the sum remainder and the public product remainder needs **27 bits** to preserve the full sum’s guessing performance for every unit product modulo 7,239,457,225. The encoder may choose a different code for each public product. **26 bits work for 14 of the 32 product patterns**. They fail on the remaining 18, because those patterns admit more than 67,108,864 different sums. The probabilities here come from uniform sampling of modular factors. [Exact widths by product](../PrimeFactors/FiveSquareSumCodeWidth.lean) · [Connection to optimal guesses](../PrimeFactors/FiveSquareSumAdviceThreshold.lean)

Why does preserving performance require distinguishing every possible sum? Suppose the helper gives two possible sums the same code. Someone receiving that code must now search for the correct pair in a list that contains candidates from both sums. Even with the best ordering, the average increases strictly whenever both sums can occur. The size of that increase varies with how frequently each sum occurs. The 27-bit result concerns **exact preservation** and puts no lower bound on a material loss from every collision. [Proof for arbitrary reports](../PrimeFactors/CompressedSumClue.lean)

A helper who can see both primes has another option. That helper can encode the position of the factor pair itself. Our previous 25-bit construction achieves a better **overall** mean than the complete sum clue using this additional knowledge. Its message identifies positions in the factor-pair list directly. Neither helper is available when the input consists of the number alone. [What 25 factor-informed bits can achieve](how-many-supplied-bits-a-factor-remainder-guess-needs.md)

## What happens when two sums share a code?

Fix the product remainder at 1 modulo 25. The sums 2 and 23 each occur for five of the 20 invertible first-factor remainders. Each of those sums has two pairs with different members and one pair with identical members.

| Sum remainder | Possible unordered pairs |
| --- | --- |
| 2 | (6, 21), (11, 16), (1, 1) |
| 23 | (4, 19), (9, 14), (24, 24) |

Reporting the exact sum costs **1.4** subsequent pair guesses on average across all 20 first factors. Reporting 2 and 23 under the same code increases the minimum to **2.05**. The other five sum remainders keep their own codes. Both merged sums occur for real prime factors. The deliberately chosen product 637,501 = 769 × 829 gives sum remainder 23, while 723,301 = 821 × 881 gives sum remainder 2. The certificates check the factorizations. The means come from exhausting the modular population. [Reproduce both means](../experiments/complementary_factor_guesses.py) · [Prime examples](../benchmarks/cases.json)

For any positive modulus and any fixed invertible product, let T count all possible first-factor remainders. In message group b let W_b count the ordered factor pairs it contains and D_b count the pairs with identical members. The optimal average is

$$
\frac12+\frac{\sum_b (W_b^2+D_b^2)}{4T}.
$$

Merging just two previously separate sum labels s and t adds precisely $(W_s W_t+D_s D_t)/(2T)$ guesses to the mean. The worked example adds $(5\times5+1\times1)/(2\times20)=13/20$. The formula counts uncertainty after the message arrives. [Exact merge cost and optimality](../PrimeFactors/CompressedSumClue.lean)
