# How much would knowing the true sum remainder help?

Suppose someone tells us the **correct remainder of the sum of the two primes** modulo 7,239,457,225. Across all distinct 1,024-bit prime pairs with a 2,048-bit product, the best average then falls to **about 48.899 guesses** for the remainder of either factor. With only the product remainder it was about 980,179,200.50. The full-size comparison assumes published Dirichlet-GRH prime-count estimates. Learning the sum remainder is an extra input in this result. The answer being guessed is still a pair of remainders modulo a 33-bit number. [Full-width comparison with the supplied clue](../PrimeFactors/FiveSquareActualSumClue.lean) · [What the product remainder alone provides](guessing-a-factor-remainder-instead-of-the-sum.md)

## A case small enough to work by hand

Modulo 25, product remainder 1 and sum remainder 2 leave the following three unordered possibilities, $\{6,21\}$, $\{11,16\}$, and $\{1,1\}$. Under uniform sampling of ordered factor remainders these have probabilities $2/5$, $2/5$, and $1/5$. Guessing the two distinct-member pairs first costs $(2+4+3)/5=9/5$ guesses on average. All three answers occur in actual small prime examples. For $723{,}301=821\times881$, the sum clue is obtained from the known primes and the answer is $\{6,21\}$. Its integer factorization certificate takes one Fermat midpoint. [The three prime products](guessing-a-factor-remainder-instead-of-the-sum.md#a-product-and-a-sum-that-fit-three-different-factor-pairs) · [Checked fixture](../benchmarks/cases.json)

## An exact count after a clue

Fix a unit product remainder $n$ modulo an odd modulus. Write $T$ for the number of units, $w_s$ for the count of ordered factor pairs with product $n$ and sum $s$, and $r$ for the number of square roots of $n$. Once $s$ is given, the remaining candidates are the unordered pairs with that particular sum. Each has one or two ordered realizations. At most one candidate can have equal coordinates, because $2a=s$ has a unique solution. Giving each sum its own best list, the optimal average is

$$
\frac{1}{2}+\frac{\sum_s w_s^2+r}{4T}.
$$

The squared weights account for how often the clue leads to a large candidate list. A sum with many compatible pairs occurs correspondingly more often. Lean proves both that no allowed policy beats the formula and that some policy attains it. The cost starts **after** the correct sum is provided. [General optimality theorem](../PrimeFactors/SumClueOrbitRanks.lean)

| Known product pattern, five prime squares | Mean with the correct sum remainder given |
| --- | ---: |
| Square at all five primes | 181.5970 |
| Nonsquare at all five primes | 8.5 |
| All unit products pooled | 48.8986274 |

Each pattern has the same number of product remainders. Across all of them, the average value of $\sum_s w_s^2$ is exactly 759,029,245,975 and the average number of square roots is 1. Substitution gives the exact modular optimum $95{,}858{,}834{,}947/1{,}960{,}358{,}400$. In the all-nonsquare case every sum has 32 ordered pairs, or 16 distinct unordered pairs, so the mean is 8.5. The all-square pattern makes the sum easier to predict, but after it is revealed the remaining factor-remainder search costs more on average. [Pattern calculations](../PrimeFactors/FiveSquareSumClueMoments.lean)

The full-width proof relates the finite modular mean to actual prime-pair frequencies. Its error in the optimal average is below 0.001 guess. For independent finite checks, exhaustive enumeration modulo 25 gives $6/5$ post-clue guesses averaged over every product and sum, and modulo 175 it gives $141/80$. [Reproduce the small counts](../experiments/complementary_factor_guesses.py) · [Published analytic estimate](https://arxiv.org/pdf/2003.01925#page=2)
