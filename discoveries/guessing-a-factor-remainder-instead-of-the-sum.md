# Guessing a factor remainder instead of the sum

Knowing the product remainder saved over 29.7758% of guesses for the **sum remainder** modulo 7,239,457,225. How much does ordering save if a guess must name the remainder of **either factor**? Across all distinct 1,024-bit primes with a 2,048-bit product, the answer is **less than one quarter of one guess on average**, using the same published Dirichlet-GRH prime-count estimate. A uniformly random order takes about **980,179,200.75** guesses. The best product-dependent order takes about **980,179,200.50**. [Full-size factor-remainder result](../PrimeFactors/FiveSquareFactorGuessing.lean) · [Sum-remainder comparison](how-predictable-is-the-sum-remainder-for-all-prime-products.md)

For this comparison both lists already use the known product. If the product remainder is $n$ and a unit remainder $a$ is one factor, the other must be $n/a$ modulo the chosen modulus. A single guess names the pair $\{a,n/a\}$. Each distinct pair appears once. The random baseline permutes these distinct pairs uniformly, so it also avoids guessing the same pair twice. The result counts the position of the hidden pair. Recognizing that a guess matches the factors of a given integer would require additional information.

## A product and a sum that fit three different factor pairs

Consider modulus 25. If the product remainder is 1 and the sum remainder is 2, the possible **unordered factor remainders** are $\{1,1\}$, $\{6,21\}$ and $\{11,16\}$. All three possibilities even occur for two distinct ten-bit primes with a twenty-bit product.

| Product | Actual primes | Factor remainders |
| ---: | --- | --- |
| 526,451 | 701 × 751 | 1 and 1 |
| 723,301 | 821 × 881 | 6 and 21 |
| 525,851 | 691 × 761 | 11 and 16 |

We chose these examples to show all three possibilities. A guess of sum remainder 2 covers five ordered residue pairs. Four come from the two distinct-remainder possibilities and one from the repeated remainder. Seeing that sum therefore leaves three possible unordered answers. Each of the actual integer products in the table is different. [Checked example](../benchmarks/cases.json) · [Enumerate the modular pairs](../experiments/complementary_factor_guesses.py)

## Where the quarter of a guess comes from

The modular calculation holds in any finite commutative group of size $T$. With a fixed product $n$, let $r$ count the solutions to $a^2=n$. There are $r$ singleton pairs and $(T-r)/2$ pairs with two distinct members. When the first factor is uniform, a two-member pair is twice as likely as a singleton. Guessing all the two-member pairs first minimizes the expected position, including the successful guess. The exact means for this product are

$$
E_{\rm best}=\frac T4+\frac12+\frac{r^2}{4T},
\qquad E_{\rm random}=\frac{T+r+2}{4}.
$$

For some fixed products, ordering saves more than a quarter of a guess. At product remainder 1 modulo 175, the saving is $29/30$ of a guess. The quarter-guess bound applies **after averaging over products**. If both factors are independent uniform units, the product is uniform. The average of $r$ is 1, because each group element squares to a single product. Every occupied square-root class has the same size $k$, the number of square roots of 1. The average of $r^2$ is therefore $k$. The mean saving over all products is exactly $(T-k)/(4T)$, strictly below $1/4$. [Fixed-product optimum](../PrimeFactors/FactorOrbitGuessRanks.lean) · [Square-root counts](../PrimeFactors/SquareFiberMoments.lean) · [Pooled theorem](../PrimeFactors/PooledFactorOrbitRanks.lean)

For the five-prime modulus, $T=3{,}920{,}716{,}800$ and $k=32$. The exact modular saving is about 0.24999999796 of a guess. The prime-pair transfer bounds the absolute error in a fixed list’s mean by $2^{-347}$. This is small enough that even a list optimized specifically for the actual prime population still saves strictly less than $1/4$ against the random baseline. The final claim uses the stated prime-count hypotheses. The finite-group formulas use no analytic assumptions. [Square roots of one at the five prime squares](../PrimeFactors/FiveSquareOrbitKernel.lean) · [Prime-counting estimate, Corollary 2](https://arxiv.org/pdf/2003.01925#page=2)

| Modulus | Best sum mean | Random sum mean | Best factor-pair mean | Random factor-pair mean | Factor-pair saving |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 25 | 35/8 | 19/4 | 221/40 | 23/4 | 9/40 |
| 175 | 207/16 | 123/8 | 3,661/120 | 123/4 | 29/120 |

The small tables enumerate every unit product and every first factor remainder. The two tasks have different answers and different numbers of possible guesses. A frequent sum remainder can group several complementary factor pairs together. [Reproduce the two tables](../experiments/complementary_factor_guesses.py)
