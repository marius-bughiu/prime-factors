# Two square questions select one of four possible prime sums modulo 144 or 288

Suppose the only input is the product $N$ of two distinct odd primes and $N$ leaves remainder 1 when divided by 12. We can write down **exactly four possible remainders for the sum of the primes**. The modulus is 144 if $N$ is 1 modulo 8 and 288 otherwise. Two yes-or-no answers about $N$ select the correct entry. Computing those answers cheaply from a general product is the outstanding step. [Exact four-entry theorem](../PrimeFactors/FourSumResidueMenu.lean) · [Precision of the selected entry](../PrimeFactors/FactorClueSumPrecision.lean)

For example, the public input **527,077** gives four candidate sum remainders modulo 288, namely **38, 70, 218 and 250**. Both square questions have answer yes for this example, choosing 38. The independently certified factors are 601 and 877. Their sum is 1,478, which is indeed 38 modulo 288. [Selected examples](../PrimeFactors/TernarySumSign.lean) · [Fermat certificate fixtures](../benchmarks/cases.json)

## Where the four entries come from

The possible prime remainders modulo 12 are 1, 5, 7 and 11. Each squares to 1, so when $pq\equiv1\pmod{12}$, **both primes have the same remainder** $a$. Write $G$ for 144 or 288 as above. The public list consists of

$$S_a\equiv a+N a^{-1}\pmod G,\qquad a\in\{1,5,7,11\}.$$

The four entries are distinct even after reduction modulo 24. Each has a modular factor pair, and every modular pair with the given product appears under one label. These witnesses establish exactly what the modular information allows. The original integer $N$ has just one unordered prime pair. Even if the correct label is supplied, no larger modulus built from powers of two and three forces a single sum remainder in this modular model. [Menu, witnesses and uniqueness](../PrimeFactors/FourSumResidueMenu.lean) · [Greatest possible modulus](../PrimeFactors/FactorClueSumPrecision.lean)

## What the two answers mean

Ask whether $-1$ is a square modulo $N$, and whether $-3$ is a square modulo $N$. For a specified integer $d$, the question means whether there is any integer $u$ such that $N$ divides $u^2-d$. The first answer tells whether the primes are 1 or 3 modulo 4. The second tells whether they are 1 or 2 modulo 3. Combining the two gives $a$. The easy Jacobi symbol of $-3$ equals $+1$ for every input here, including inputs on which the square does not exist. [Square test for minus one](../PrimeFactors/QuarticLocalSquareCriterion.lean) · [Square test for minus three](../PrimeFactors/TernarySumSign.lean)

| $-1$ square | $-3$ square | Common factor remainder mod 12 | Chosen product | Certified primes | Actual sum mod 288 |
| --- | --- | ---: | ---: | --- | ---: |
| Yes | Yes | 1 | 527,077 | 601 × 877 | 38 |
| Yes | No | 5 | 649,333 | 641 × 1,013 | 214 |
| No | Yes | 7 | 679,141 | 739 × 919 | 218 |
| No | No | 11 | 553,429 | 563 × 983 | 106 |

These four deliberately selected products all have 20 bits, consist of two 10-bit primes and equal 37 modulo 432. Their ordinary Fermat runs take 13, 22, 5 and 30 midpoint tests in table order. The table verifies that all four combinations occur. It uses the factors to establish the answers. [Lean examples](../PrimeFactors/TernarySumSign.lean) · [Independent replay inputs](../benchmarks/cases.json)

The second answer alone selects one sum remainder modulo nine, with $S\equiv N+1$ for yes and $S\equiv-(N+1)$ for no. At modulus 27 there are exactly two possibilities per sign. For a yes answer they are $N+1$ and $N+10$ if $N\equiv1\pmod9$, or $N+1$ and $N-8$ otherwise. Negate both for a no answer. Each possibility has modular witnesses. [Exact ternary menu](../PrimeFactors/TernarySumSign.lean)

## How much can the product remainder predict at full size?

Fix the product remainder modulo 48 to any one of 1, 13, 25 or 37. Among all products of two distinct 1,024-bit primes having 2,048 bits and that specified remainder, each of the four labels has frequency within $1/2080$ of one quarter. Each label gives a different sum modulo 48. A guess using only that product remainder therefore succeeds at most **25.049%** of the time. A rule using other bits of the product would require a separate analysis. Lean verifies this population comparison with the published unconditional prime-count estimate entered as a hypothesis. [Full-size population theorem](../PrimeFactors/JointSumSignPopulation.lean) · [Bennett, Martin, O’Bryant and Rechnitzer, Theorem 1.3](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf#page=5)

The distinction between a residue count and a frequency matters when combining more answers. For pairwise coprime moduli, suppose each yes-or-no label is determined by the local sum and reverses when the sum is negated. Across a complete period, any prescribed vector of $k$ labels then retains exactly $1/2^k$ of the **distinct admissible sums**. For a product equal to 1 modulo 231, the square or nonsquare status of a factor at 3, 7 and 11 selects six of 48 allowed sum residues for each answer vector. The theorem counts distinct remainders, and obtaining the answers costs extra. [General count and eight verified outcomes](../PrimeFactors/IndependentSumSignCounts.lean)
