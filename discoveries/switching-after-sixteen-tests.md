# Where to search after sixteen ordinary square tests

Suppose two unknown 1,024-bit primes multiply to a public number $N$. In a specific range of products, a change of search after sixteen ordinary tests visits a wider part of the possible factor range. For six of the eight possible remainders modulo 24, switching covers more integer locations. For the other two, continuing the ordinary search covers more. The same decision works even when we count only locations in one chosen remainder class. Both searches missed the factors of the two full-size examples examined below. [Width and integer-count proofs](../PrimeFactors/MarginalTraceWidth.lean) · [Connection to the tested labels and gcd](../PrimeFactors/MarginalTraceCoverage.lean)

## What the search checks

Put $U=2^{1024}$. The result applies when $9U^2/16\le N\le5U^2/8$ and $N$ is coprime to six. Start by looking for the unknown sum $p+q$ using the first sixteen admissible integers above or equal to $2\sqrt N$. At a candidate sum $S$, test whether $S^2-4N$ is a square. Then choose one of two continuations.

- Continue with seventeen more candidate sums $p+q$.
- Switch to the first sixteen candidates for $3p+2q$ above or equal to $2\sqrt{6N}$. At each candidate $S$, test whether $S^2-24N$ is a square.

Each route takes 34 integer square roots when run to its full budget. The first uses one to find its starting point and 33 for square tests. The second uses two starting roots and 32 square tests. This accounting omits additions, multiplications, residue tests and gcds. The constants and both starting points depend only on $N$.

For weights $(a,b)$ an admissible integer satisfies $\gcd(S,24)=\gcd(a+bN,24)$. The true weighted sum obeys this rule because $p$ is invertible modulo 24 and $p^2\equiv1\pmod{24}$. At $S=ap+bq$, the discriminant is exactly $(ap-bq)^2$. The gcd of $(S+\sqrt{S^2-4abN})/2$ with $N$ recovers one factor for either of the two choices of weights. [Admissibility, intervals and recovery](../PrimeFactors/MarginalTraceCoverage.lean) · [Gcd proof](../PrimeFactors/WeightedTracePrefix.lean)

## Which integer locations count

A location $x$ is covered if a true smaller factor at $x$ would have its weighted sum tested. To compute the bounds, let $z$ be the **first omitted admissible label**. For positive $x$, the inequality $ax+bN/x<z$ picks out an open interval. For integer $x$, set $R=\lfloor\sqrt{z^2-4abN-1}\rfloor$. The first and last integers in the interval are $L=\lceil(z-R)/(2a)\rceil$ and $H=\lfloor(z+R)/(2a)\rfloor$. This rounding handles exact-square boundaries. [Integer endpoint identities](../PrimeFactors/WeightedTracePrefix.lean)

Write $L_i,H_i$ for those endpoints when the first $i$ labels have been tested. The ordinary continuation covers $L_{33}$ through $L_{16}-1$, using weights $(1,1)$. The switch covers $L_{16}$ through $H_{16}$ using $(3,2)$. Throughout the stated range of products, this second interval lies between $0.80\sqrt N$ and $0.83\sqrt N$, entirely within the range allowed by the two bit lengths. The ordinary interval is above $0.99\sqrt N$. These wider enclosing bounds describe where to find each interval. Its exact width is much smaller.

Measuring width by the logarithm of the ratio of the upper to lower endpoint, the switch wins for every eligible product. Counting ordinary integers, the proof gives a strict gain for $N\bmod 24\in\{1,5,7,13,17,19\}$. For remainders 11 and 23, continuing the ordinary search instead covers strictly more integer locations. In those two cases consecutive ordinary labels are 24 apart, so seventeen more tests reach farther down the range. Neither width measures the probability that a prime in the interval divides this particular product. No prime-distribution hypothesis is used in these comparisons. [Lean comparison](../PrimeFactors/MarginalTraceWidth.lean)

This choice survives earlier modular filters. Write $u=N^{1/4}$. For the first six remainders the switch gains more than $u/4$ in ordinary interval length. For the other two, ordinary continuation gains more than $u/20$. Even after restricting locations to any single remainder modulo any $1\le M\le2^{500}$, the same choice wins in integer counts. To see why, a progression of spacing $M$ has boundary rounding error of at most one location at either end, and the interval length advantage exceeds $2M$. One can also sum over any nonempty collection of allowed remainders modulo the same $M$. This measures additional locations checked under a shared filter. Searching for a divisor on those inputs remains a separate problem. [Exact comparison for each integer progression](../PrimeFactors/MarginalTraceCoverage.lean)

| Published 2,048-bit product in the range | Extra ordinary locations | Switch locations | Square hits on either route |
|---|---:|---:|---:|
| Constructed near the 3-to-2 ratio | $5.049\times10^{154}$ | $8.628\times10^{154}$ | 0 |
| Crossed comparison | $4.858\times10^{154}$ | $8.477\times10^{154}$ | 0 |

The counts in the table are rounded from the integer endpoint formulas above. On the constructed example, the longer search eventually found the primes on its 15,264th odd label. Sixteen admissible labels did not reach them. The fresh comparison product falls outside the product range of this theorem. [Decimal products](../benchmarks/interior-prime-family.json) · [Longer search and its certificate](switching-after-a-long-fermat-search.md#a-constructed-2048-bit-example)
