# What a modulus budget allows a guess order to save

Could higher prime powers, or a mixture of small and large primes, make the true sum remainder easy to guess? Fix any positive integer modulus $m\le 2^{2048}$ and any product $n$ coprime to $m$. Choose one of the ordered pairs $(a,b)$ with $ab=n\pmod m$ uniformly. A list names each attainable remainder of $a+b$ once and pays its position in the list, including the successful guess.

| Permitted modulus | Cost every guess order must exceed |
| --- | ---: |
| A product of distinct odd prime squares | 7.581413% of the random-order mean |
| Any odd modulus, including arbitrary prime powers | 1/64 of the random-order mean |
| Any positive modulus | 1/1,024 of the random-order mean |

The stronger figure of **at least 1.89535325%** holds for odd moduli whose prime exponents are all at least two. In that case, a list covering **99.9%** of the modular factor pairs must include **more than 94.72%** of the attainable sum remainders. The random-order comparison always uses the same modulus and the same possible sums as the order under study. The bounds concern a population of remainders at a fixed product residue. They give neither factors of a particular integer nor a lower bound on general integer factorization. [All positive moduli](../PrimeFactors/AnyModulusGuessFloor.lean) · [Odd moduli](../PrimeFactors/AllOddGuessFloor.lean) · [Higher powers and coverage](../PrimeFactors/DeepBudgetedSumGuesses.lean) · [Prime-square case](what-many-prime-squares-buy-a-remainder-guess.md#what-if-the-modulus-must-fit-a-2048-bit-budget)

## Why arbitrary powers still admit a bound

At an odd prime alone, an attainable sum can correspond to one or two ordered pairs. The two possibilities arise from interchanging the factors. At higher precision, the weight of an attained sum is at least the weight of its projection modulo the prime square. The project already bounds the total loss in the **fraction of sums that remain attainable** as precision increases across several primes. Combining these facts gives a guaranteed uniform component in the distribution for the block of higher powers. [Weight under projection](../PrimeFactors/PrimePowerWeightMonotone.lean) · [Uniform share of the higher-power table](../PrimeFactors/PrimePowerUniformShare.lean)

For the first-power block the proof uses a different statistic. Given two labels of weights $w_x,w_y$, sum $\min(w_x,w_y)$ over all ordered choices of labels. This quantity bounds the mean guess rank even when one label is unusually unlikely. If the weights are one or two, there is an exact formula. With $A$ labels and total weight $T$, the sum of the pairwise minima is $A^2+(T-A)^2$. The corresponding lower bounds multiply when two coprime moduli are combined. [Local formula](../PrimeFactors/FirstPowerGuessOverlap.lean) · [Guess rank and combining tables](../PrimeFactors/GuessTableOverlap.lean)

Every odd prime used in the modulus consumes part of the common budget. Even counting each prime only once, at most **231 distinct primes of size five or more** fit. Multiplying their worst local coefficients still gives more than 1/16. Allowing arbitrary depths costs at most another factor of four in this argument, giving 1/64. [Finite certificate](../PrimeFactors/GuessRadicalBudget.lean)

For powers of two, all odd products admit a uniform component of at least 1/16. One tempting stronger estimate already fails at modulus **2,048**. When the product remainder is 1, 46 different sum remainders occur. The sum remainder 46 has 16 of the 1,024 ordered pairs, so it receives exactly **23/32** of the probability it would have in a uniform table of 46 sums. This is below 3/4. Combining the 1/16 guarantee with the odd-modulus bound gives the row for arbitrary moduli. [All powers of two and the counterexample](../PrimeFactors/TwoPowerGuessShare.lean)

A chosen integer example is $2{,}729{,}551{,}873=51{,}803\times52{,}691$. Its product and sum have remainders 1 and 46 modulo 2,048. Its factors are close, so the separate Fermat certificate needs two midpoints. The modular proof counts the 16 ordered pairs without using this example. [Checked benchmark](../benchmarks/cases.json)
