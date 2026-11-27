# Why a factor-sum spacing of 20,160 always survives

Suppose we have a list of guesses for the sum of two unknown primes. At each guess we test whether two remainders can add to that guess and multiply to the known product. We can do this modulo any positive integer. **Two guesses 20,160 apart can both pass, somewhere in the list of remainders, for every product and every modulus.** The same holds for every multiple of 20,160. No other integer spacing has that guarantee. [Full Lean theorem](../PrimeFactors/UniversalSumStride.lean)

For example, 45 guesses left only two survivors in a small factorization. The new theorem limits how far we could generalize that success by choosing a cleverer modulus. For a run of 20,161 consecutive guesses, some starting position permits two survivors whatever modulus we choose. The starting position can depend on the product and the modulus. A particular block with a known starting position may still contain just one survivor, or none. Both survivors in the theorem have local factor pairs. They need not give two integer factorizations. [The two-out-of-45 example](how-many-factor-sums-pass-together.md)

## Where the number comes from

| Prime powers used for the test | Spacings that work for every product at all depths |
| --- | --- |
| Powers of 2 | Multiples of 64 |
| Powers of 3 | Multiples of 9 |
| Powers of 5 | Multiples of 5 |
| Powers of 7 | Multiples of 7 |
| Powers of a prime at least 11 | All spacings |

For powers of two, products congruent to 3 modulo 4 allow every spacing divisible by eight. The class 5 modulo 8 allows just three spacing classes modulo 32. The class 1 modulo 8 has a square root, which lets us reduce the calculation to product 1. The proof there reduces the remaining question to a sum of two squares and low-bit tests. At modulus 64 alone the three product residues 1, 5 and 59 have only spacing zero in common. [Two-adic proof](../PrimeFactors/TwoAdicSumSpacing.lean)

For powers of three, consider product 1. Sums of the form $2+9a^2$ are locally possible, since their discriminants are $9a^2(4+9a^2)$ and the last factor has a square root at every power of three. Every residue is a difference of two squares when 2 is invertible, so differences of these sums cover every multiple of nine. Scaling deals with other square products, and the proof also treats nonsquare and zero residues. The two product residues 1 and 2 already exclude every other universal spacing modulo 9. [Three-adic proof](../PrimeFactors/ThreeAdicUniversalSpacing.lean)

At 5 and 7 there is always at least one pair of distinct factor residues for the chosen product. The sum of such a pair continues to work after adding any multiple of the prime at higher precision. At primes from 11 onward every spacing already works at every depth. The Chinese remainder theorem combines all components, giving $64\times9\times5\times7=20,160$. [Small-prime lift](../PrimeFactors/UniversalSumStride.lean) · [Large-prime theorem](../PrimeFactors/FactorSumSpacing.lean)

## Does the same limit hold at 2,048 bits?

Yes. We checked three products of distinct, certified 1,024-bit primes. Each product has exactly 2,048 bits. Their remainders are all that the sharpness proof needs.

| Product | Modulo 64 | Modulo 9 | Modulo 5 | Modulo 7 |
| --- | ---: | ---: | ---: | ---: |
| First | 1 | 4 | 3 | 5 |
| Second | 5 | 8 | 1 | 3 |
| Third | 59 | 7 | 2 | 6 |

At each of the four moduli, only zero can be a spacing for all three rows. Together with the general theorem, this proves exactly the same classification when we restrict the inputs to balanced 2,048-bit products. The certificates use known primes to prove the restriction is sharp. They do not recover primes from a new product. [Reproduce the full-width certificates](../experiments/full_width_totient_divisor.py)

## How much information could this save?

One proposed decoder reads a single base-$M$ digit of a polynomial value. That digit partitions a public interval of candidate sums into evenly spaced lists. We asked whether clever remainder tests could make a small digit sufficient by guaranteeing at most one survivor in every translated list. This calculation grants the polynomial digit for free. Computing it cheaply from the product is still open. [Definition of the digit and the public interval](two-ways-to-read-the-prime-sum.md)

On the two published 2,048-bit comparisons, the limit can be calculated from the product and the advertised factor width alone. The table gives bit lengths of the *modulus* $M^2$ used to request the digit.

| Input | Direct decoder | Smallest modulus size allowed by the new necessary condition |
| --- | ---: | ---: |
| Fresh | 2,030 bits | 2,008 bits |
| Crossed | 2,036 bits | 2,012 bits |

Even the lower figure only clears a necessary arithmetic condition. We do not know a decoder that achieves it. For any input, the direct decoder's squared modulus is less than $2^{25}$ times the squared modulus of any radix meeting this condition. On the fresh comparison this leaves at most 22 bits to save by this argument. On the crossed comparison it leaves at most 24. [Exact numerical receipts and general comparison](../PrimeFactors/UniversalPackingBudget.lean)

To see the bound, let $W$ be the spacing between initial candidates given by the product modulo 12, and let $C$ be their number. A digit separates the positions into $P=M/\gcd(M,W/2)$ classes. Within each class the spacing in the sum becomes $WP$. After $20160/\gcd(20160,WP)$ steps the difference is a multiple of 20,160, so a uniqueness guarantee valid at every starting point must stop there. Multiplying the permitted class length by $P$ gives the necessary inequality

$$
C\ \le\ \frac{20160}{W}\,\frac{M}{\gcd(M,10080)}.
$$

We also counted how often a genuinely small digit could meet this requirement. Among all unordered pairs of distinct 1,024-bit primes whose product has 2,048 bits, **fewer than one in $2^{920}$** admit such a uniform window with any modulus and any radix up to $2^{64}$. With a radix up to $2^{128}$ the fraction is **below one in $2^{856}$**. An interval small enough to qualify forces both primes very close to the largest 1,024-bit integer. Counting even the composite odd integers in that small region gives the upper bound. A method that exploits the actual start or additional information about the product falls outside this result. [Formal connection to the uniqueness test and exact population bounds](../PrimeFactors/SmallRadixPackingPopulation.lean)

The distinction matters for the earlier work using the Dirichlet generalized Riemann hypothesis. There the discriminant of a *specified* candidate determines a quadratic character, and the analytic estimate bounds how far to look for a prime that rejects a nonsquare. Here the test knows the *distance* between guesses and promises to work at every starting position. Both the spacing classification and the population bounds above are unconditional. [Earlier discriminant test and its analytic assumptions](reconstructing-winning-positions.md)
