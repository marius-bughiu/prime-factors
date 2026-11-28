# How many factor sums can a list of guesses cover?

Suppose we read the last 161 bits of the product of two 1,024-bit primes. We want to predict the last 161 bits of their sum. We can make **4,294,967,296 distinct guesses**, tailored to the exact product ending we read. How often can even the best list contain the right answer?

| Last three product bits | Best chance of including the true sum ending |
| --- | --- |
| 001 | About **one in 3.95 quintillion** |
| 101 | About one in $2^{125}$ |
| 011 or 111 | About one in $2^{126}$ |

Each row applies separately to **every fixed 161-bit product ending** of the indicated kind. We count every unordered pair of distinct 1,024-bit primes with that ending and a 2,048-bit product once. The numbers in the table are exact for uniform modular factor pairs before rounding the first row. For actual primes, each fraction has relative error at most $2^{-146}$ under the explicit prime-count estimates described below. A hit supplies a sum ending. The rest of the sum and the two integer factors are still unknown. [Exact 001 result](../PrimeFactors/ExactDyadicSumMenu.lean) · [Other endings](../PrimeFactors/DyadicFlatSumMenus.lean) · [Prime-population comparison](../PrimeFactors/DyadicMenuPopulationOptimum.lean)

## A list small enough to check by hand

Take the product remainder 65 modulo 512. Any of the 256 odd first-factor residues is possible. Each determines one partner because it is invertible modulo 512. Count the 256 resulting sums, allowing the two orders of a pair to count separately. Only 14 sum endings occur. Two occur 32 times each. Each of the remaining twelve occurs 16 times. With room for five guesses, the best total is $2\times32+3\times16=112$ pairs, or **43.75%**. [Lean enumeration and proof of optimality](../PrimeFactors/SumMenuSmallExamples.lean)

| Product remainder modulo 512 | Two most frequent sums | One optimal five-guess list | Pairs covered |
| ---: | --- | --- | ---: |
| 65 | 130, 382 | 130, 382, 18, 66, 110 | 112 of 256 |
| 209 | 210, 302 | 210, 302, 30, 98, 110 | 112 of 256 |

The same list size buys the same coverage for these two product endings. The actual sums to put on the list differ. These examples count all modular possibilities and need no prime-distribution estimates. [Five-guess examples](../PrimeFactors/SumMenuSmallExamples.lean)

## What makes a sum worth guessing

Fix an odd product remainder $n$ modulo $2^e$. If two odd factor residues $a,b$ first differ after $u$ matching low bits, the number of ordered pairs with their product and sum is $2^{u+1}$ when $e>2u$, and $2^{\lfloor e/2\rfloor}$ otherwise. If $a=b$ modulo the entire modulus, the second count applies. This counts how many possible pairs a guess covers. For the pair $(9,1)$, for example, the count at five, six, seven and eight bits is respectively 4, 8, 16 and 16. [Exact multiplicity](../PrimeFactors/DyadicPairSumWeight.lean)

For $n\equiv1\bmod8$, we can group the sum labels by the number of matching factor bits. Write $e=2t+j$ with $t\ge2$. The group containing every pair whose factors agree in at least $t+1$ bits has exactly twice as many labels as there are distinct square residues modulo $2^j$. Its total weight is exactly $2^{t+j+1}$. The labels can be defined using the public product remainder. Membership is the condition that the half-sum $h$ has $h^2-n$ divisible by $2^{2t}$, among sums supported by a pair. [Construction and counts](../PrimeFactors/DyadicClusterMenu.lean)

At 161 bits, the first 2,863,311,534 labels needed here cover $2^{98}$ pairs. Each of the next 1,431,655,762 guesses covers exactly $2^{65}$ more. Every omitted guess offers at most that weight, and there are enough labels at that weight to fill the list. Dividing the total by the $2^{160}$ possible ordered pairs gives the exact fraction

$$\frac{2^{98}+1{,}431{,}655{,}762\,2^{65}}{2^{160}}=\frac{5{,}010{,}795{,}177}{2^{94}}.$$

A single best guess covers a fraction $2^{-79}$. Four billion guesses improve the chance by a factor of about **152,917**. The highest weights occur too infrequently for all guesses to be as valuable as the first. This proof gives the optimum even if choosing and storing the list cost nothing. [Optimality for this budget and every intermediate group size](../PrimeFactors/ExactDyadicSumMenu.lean) · [Single-guess optimum](when-one-public-square-root-predicts-the-prime-sum.md)

## What if the rest of the product supplies a clue?

Keep a fixed product ending in 001 and the same limit of $2^{32}$ guesses. Allow a further clue to choose which list to use. It could be any function of the entire product. With **121 additional bits**, even a perfectly chosen clue can hit fewer than **41.7%** of the prime pairs in the class. With **122** perfectly chosen bits, more than **58.3%** is mathematically attainable. These prime-population figures use the same endpoint estimate. [Threshold for auxiliary information](../PrimeFactors/DyadicSumAdviceThreshold.lean)

The distinction matters for the factoring question. With $k$ clue bits there are at most $2^k$ different lists, covering at most $2^{k+32}$ sum endings between them. Conversely, one can divide a large list into blocks and supply the number of the block containing the correct answer. This construction allows the supplier to know the true sum. Getting a suitable block number cheaply from the rest of the product is an open computational question. A count of bits alone supplies no such rule. [Finite-list and advice equivalence](../PrimeFactors/FiniteAdviceMenus.lean)

## Where the prime estimates enter

Across **all** eligible prime pairs, an unconditional count proves that fewer than **one in $2^{45}$**, or one in 35 trillion, can be hit. The list may be chosen differently for every 161-bit product ending. To bound how many full-size primes can have a specified residue, we count the integer positions left after removing multiples of 3, 5, 7, 11 and 13. Summing over the possible residue pairs and using an unconditional lower bound on the full prime-pair population gives this looser bound. [Unconditional population proof](../PrimeFactors/UnconditionalSumMenuPopulation.lean) · [Denominator](../PrimeFactors/ChebyshevPrimeSample.lean)

The exact modular optimum and all finite multiplicities above follow from arithmetic modulo powers of two. Transferring them to actual 1,024-bit primes in **one specified** product class uses the explicit estimates for primes in arithmetic progressions of Ernvall-Hytönen and Palojärvi. Lean takes the two endpoint bounds as premises and proves both the upper bound for every list and existence of a list attaining the claimed accuracy. The verified Dirichlet GRH theorem supplies the hypothesis in the analytic paper. A formal deduction of the paper's endpoint bounds from the upstream Lean theorem remains open. [Conditional transfer for any list](../PrimeFactors/DyadicSumMenuBudget.lean) · [Transfer of the optimum](../PrimeFactors/DyadicMenuPopulationOptimum.lean) · [Ernvall-Hytönen and Palojärvi, Corollary 2](https://arxiv.org/pdf/2003.01925#page=2) · [Independent check of the Dirichlet theorem](https://math.mit.edu/~drew/shortgrh/)
