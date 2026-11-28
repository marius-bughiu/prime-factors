# Can changing the primes avoid the wrong sums?

Suppose the search can read the product and choose a different list of prime tests for each input. **For almost every eligible 2,048-bit product, every list within the period budget below still leaves more than $2^{765}$ wrong sums ahead of the true sum.** Compared with the previous result for the first 117 primes, this also covers lists containing larger primes. The wrong sums can be different for each list. [Pre-success theorem with one common exceptional set](../PrimeFactors/PrimeMenuScorePrefix.lean)

The search orders candidate sums by their location and their remainder, as before. Keep the tests at 2, 3 and 5. Choose any additional distinct primes. Write $S$ for the chosen primes at least 5, including 5 itself. The budget is

$$M=128\cdot27\prod_{p\in S}p\ \le\ W=2^{896}.$$

This measures whether a full period of the guaranteed residue classes fits in the early interval of $W$ midpoints. Each listed prime may still be tested to **unlimited precision**. The list can change with the product. Within an individual search, the proof covers tests at any of the primes on its list, in any order and to any depth, depending on the candidate. The result applies to all unordered pairs of distinct 1,024-bit primes with a 2,048-bit product except for fewer than one pair in $2^{35}$. It leaves open lists whose combined period exceeds the budget, or another way to skip candidates. [Earlier result and definition of the search order](wrong-sums-before-the-search-can-stop.md)

## Which list gives the smallest guaranteed count?

Let $C$ consist of the 115 primes from 5 through 643. For any allowed list define

$$R(S)=8\prod_{p\in S}\frac{p-3}{2},\qquad B(S)=\left\lfloor\frac{W}{M}\right\rfloor R(S).$$

Every complete period supplies at least $R(S)$ different midpoints whose discriminants have roots at every power of every chosen prime. The formula for $B(S)$ counts only classes guaranteed in complete periods. It can underestimate the actual number of survivors. **The list $C$ attains the minimum of this formula across all allowed lists**, and that minimum exceeds $2^{765}$. [Proof for an arbitrary list](../PrimeFactors/ArbitraryMidpointMenu.lean) · [Minimum and attainment](../PrimeFactors/PrimeMenuPeriodMinimum.lean)

There are two cases. Buying a 116th prime would make the product too large, even with the smallest possible choices. With exactly 115 primes, replacing any of the initial primes by a larger one increases or preserves the factors $(p-3)/2$ in the class count, and at least one period fits. With fewer than 115 primes, the guaranteed *fraction* of survivors at least doubles compared with $C$. Each omitted prime has local fraction $(p-3)/(2p)<1/2$, and replacing a smaller prime by a larger one only increases this fraction. Complete periods cover at least half of the window, which is enough to retain the original guarantee. [Local density and cardinality comparison](../PrimeFactors/PrimeMenuDensityOrder.lean)

## A smaller case where every list can be checked

With $W=2^{21}$ and the same compulsory primes, there are 31 admissible lists. The smallest formula value is 64, reached only by $S=\{5,7,11\}$. The other two three-prime choices give 80 for $\{5,7,13\}$ and 112 for $\{5,7,17\}$. The smallest value among shorter lists is 232 for $\{5,61\}$. [Reproduce the complete menu census](../experiments/prime_menu_period_minimum.py)

For $16{,}637=127\times131$, midpoint 399 passes every power of 2, 3, 5, 7 and 11, but fails modulo 13. Midpoint 1,089 passes every power with 13 in place of 11, but fails modulo 11. These two midpoints illustrate that changing the list can change *which* guesses survive. The actual midpoint is 129, and both examples are outside the pre-success interval. [Reproducible local square checks](../experiments/prime_menu_period_minimum.py)
