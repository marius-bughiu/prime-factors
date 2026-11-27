# Which primes can separate two possible factor sums?

Take a product whose remainder on division by 5 is 3. Its factors can have remainders 1 and 3, or 2 and 4, in either order. Their sum therefore ends up at 4 or 1 modulo 5. Two guesses for the sum that differ by one cannot both pass this test, wherever the guesses start. This observation helped us distinguish four guesses in a small factoring example. [The four guesses for 7,294,033](two-ways-to-read-the-prime-sum.md)

Can a larger prime supply another rule of this kind? **Only 2, 3, 5 and 7 can forbid a fixed distance between two possible sums.** For every prime from 11 onward, every product remainder and every proposed distance, there is some starting point where both sums pass. The same holds if the modulus is built entirely from powers of primes at least 11. Larger primes can still rule out individual guesses once their actual values are specified. [Prime and prime-power theorem](../PrimeFactors/FactorSumSpacing.lean) · [Combining moduli](../PrimeFactors/FactorSumSpacingCRT.lean)

## All the exceptions at prime moduli

Each distance and product in the table is a remainder modulo the prime in the first column. A product remainder absent from that column's cases allows every distance.

| Prime | Product remainder | Distances that cannot occur |
| ---: | ---: | :--- |
| 2 | 1 | 1 |
| 3 | 2 | 1, 2 |
| 5 | 2 | 2, 3 |
| 5 | 3 | 1, 4 |
| 7 | 3 | 2, 5 |
| 7 | 5 | 3, 4 |
| 7 | 6 | 1, 6 |

Lean checked the table exhaustively. As a separate check, we enumerated all pairs of factor residues at the 30 primes through 113 and at the composite moduli 121, 169, 187 and 209. [Checked exception table](../PrimeFactors/FactorSumSpacingSmall.lean)

The single product $713=23\times31$ illustrates all four exceptions. Its remainders modulo 2, 3, 5 and 7 are respectively 1, 2, 3 and 6, so every one of the four tests excludes a distance of one. Any modulus divisible by one of these primes inherits that failure. Consequently a positive modulus allows every spacing for every product exactly when it is coprime to 210. [Exact classification](../PrimeFactors/UniversalSpacing.lean)

## Why the list ends at seven

Fix a prime $\ell\ge11$ and a nonzero product remainder $n$. Choosing a nonzero first factor $x$ determines the second as $n/x$. Write $A$ for the set of distinct sums $x+n/x$. If $n$ is a square, more than half of all residues belong to $A$. Two copies of a set that large must overlap, however far one copy moves. If $n=0$, the pair $(0,s)$ realizes every sum $s$.

If $n$ is a nonsquare, $A$ has exactly $(\ell-1)/2$ members. Suppose some distance were missing. Moving $A$ by that distance would give a second, disjoint set, leaving exactly one residue uncovered. Write $M_j$ for the sum of the $j$th powers of the members of $A$, computed modulo $\ell$. Adding the first four powers over the sets and the uncovered point forces $M_4=-10M_2^2$, since the first and third moments vanish. Directly summing the factor expressions gives $M_2=-n$ and $M_4=-3n^2$. The two equations imply $7n^2=0$ modulo $\ell$. A prime at least 11 cannot divide 7 or the nonzero residue $n$. [Identity for a missing distance](../PrimeFactors/TraceGapCycle.lean) · [Moments from the product](../PrimeFactors/TraceGapMoments.lean)

For powers of a prime we also need the locally possible sums to lift to the higher modulus while keeping their distance. The square-product case requires particular care because the two associated factor residues can coincide. The proof chooses witnesses with at least one pair of distinct factors. The Chinese remainder theorem then combines the prime-power witnesses. These constructions produce modular factor pairs. Discovering the actual integer primes from their product remains open for the general 2,048-bit case. [Square-product lifting argument](../PrimeFactors/SquareTraceGapLift.lean)

Bower, Evans, Luo and Miller study possible coordinate sums $x+y$ and coordinate differences $x-y$ on the modular hyperbola $xy=n$. Here the distance is between sums belonging to two potentially different pairs on that same hyperbola. [Related paper](https://arxiv.org/abs/1212.2930)
