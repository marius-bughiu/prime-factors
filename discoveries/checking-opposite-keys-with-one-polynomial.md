# Checking opposite keys with one polynomial

On the fresh 2048-bit product, checking 512 random inputs took **0.97 CPU seconds** using polynomial division, **1.25 seconds** multiplying every pair sum, and **1.70 seconds** using the earlier polynomial evaluation tree. All three searches missed the factors. On smaller products the division also exposed 13 factors on inputs with no matching pair. [Measurements and individual runs](../research/opposite-key-comparison.json)

## What polynomial division detects

The input is a product of two distinct primes greater than 864 whose product leaves 5 or 7 modulo 12. For a regular sample, let $v_i$ be its public modular label and put $t_i=2v_i-1$. Two labels sum to one modulo a prime precisely when their $t_i$ values are opposites there. Only one of the two primes can support complementary labels. The earlier search built a polynomial with roots $t_i$, evaluated its reflection at every sample, then took a gcd. An elementary comparison multiplies $v_i+v_j-1$ modulo the product for all $i\le j$ and takes one gcd. Both include a sample paired with itself. [Complementary label theorem](../PrimeFactors/ComplementaryKeys.lean) · [Implementations](../experiments/complementary_keys.py)

The new method builds the same polynomial $F(X)=\prod_i(X-t_i)$. The gcd of its constant coefficient with the input checks for a zero root. Otherwise, group the even and odd powers as $F(X)=E(X^2)+X O(X^2)$. Lean proves that over a field of characteristic different from two, with all $t_i$ nonzero, an opposite pair exists exactly when $E$ and $O$ have a common polynomial divisor of positive degree. The proof covers repeated roots. The Python search runs Euclidean division modulo the composite input. A leading coefficient that cannot be inverted can itself reveal a prime, even if neither field has an opposite pair. The field theorem does not predict the frequency of those extra factors. [Lean equivalence](../PrimeFactors/OppositeKeyPolynomial.lean) · [Euclidean implementation](../experiments/opposite_key_polynomial.py)

Lean also checks what exact division identities preserve. In either prime field, the last polynomial in a division ending at zero has exactly the common divisors of the two starting polynomials. If just one field has opposite nonzero roots, the last polynomial's leading coefficient cannot be invertible modulo the product. Any nonzero coefficient that fails this invertibility test gives a proper divisor by a gcd, including at an earlier division step. These statements apply to exact division traces. The Python implementation is checked separately on the finite panel below. [Division trace and proper-divisor proofs](../PrimeFactors/OppositeKeyDivision.lean)

## Full search time on the fresh product

Each cell gives median **CPU / wall seconds** across the same three fixed random seeds. At every budget the three methods rotated through first, second and third place in the run order. Timing started before drawing any samples and included the regularity mask, its gcd, label normalization and all polynomial or pair arithmetic. All samples passed setup on this product. The 45 runs found no factor. [Input generation](certified-fresh-control.md) · [Per-seed timings and work counts](../research/opposite-key-comparison.json)

| Draws | Pair sums | Euclidean division | Reflected evaluation tree |
| ---: | ---: | ---: | ---: |
| 32 | 0.011 / 0.011 | 0.016 / 0.016 | 0.025 / 0.025 |
| 64 | 0.031 / 0.031 | 0.039 / 0.039 | 0.071 / 0.072 |
| 128 | 0.100 / 0.102 | 0.109 / 0.112 | 0.210 / 0.214 |
| 256 | 0.352 / 0.360 | 0.307 / 0.311 | 0.593 / 0.598 |
| 512 | 1.249 / 1.255 | 0.971 / 0.982 | 1.701 / 1.709 |

At 512 samples each method spent one gcd on the masks and one inversion to normalize the labels. The direct test then multiplied 131,328 terms modulo the input and took one gcd. Both polynomial methods built a tree of 511 polynomial products. The reflected evaluation used 512 evaluations and one final gcd. Euclid instead made 255 additional inversions, 65,280 coefficient updates and two gcds. These counts and timings describe the measured Python implementations. They give no estimate of the time until a 2048-bit factor will turn up. [Panel code](../experiments/opposite_key_comparison.py)

## Which small products split?

We replayed the same twelve draws per product from the earlier census on **all 9,804** mixed 24-bit products of distinct 12-bit primes. A separate calculation using the known primes checked every setup result and every potential complementary match. The direct product and reflected tree agreed with it on all 9,804. Both found 690 factors at setup and 2,152 through complementary labels. Euclid split all 2,842 of those products and **13 more**, for 2,855 in total. On three of the 2,152 words with a complementary match, an early leading coefficient revealed the other prime. [Census, source counts and replay seeds](../research/opposite-key-comparison.json)

For example, Euclid found **3,947 × 2,143 = 8,458,421** even though none of the twelve regular labels had a complementary partner at either prime. On **8,635,483 = 2,801 × 3,083**, the labels had a complementary match modulo 3,083 but the first noninvertible leading coefficient exposed 2,801. Run `python3 -m experiments.opposite_key_comparison` for the timed panel and `python3 -m experiments.opposite_key_comparison --check-census` to replay the small population and verify every returned prime factorization in Lean. [Panel and certificate generator](../experiments/opposite_key_comparison.py)
