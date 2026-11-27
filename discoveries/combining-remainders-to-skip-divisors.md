# Combining remainders to skip possible divisors

Starting with 246,180,296,426,219 and the information that both primes have 24 bits, we found three clues about the divisors. Together they cut the repeating list of possible positions from 1,920 to 240. Jumping directly to those positions found **15,230,737 × 16,163,387** in 14,474 divisions. The same search without the clues needed 115,793. A search over possible *sums* was already quicker on this example. On both 2,048-bit comparison inputs the first 256 remainders gave zero clues of this kind.

## Where a clue comes from

A small example uses only two remainders. For $N=5{,}459$, the continued fraction of $\sqrt{4N}$ gives $1938^2\equiv52$ and $693^2\equiv-143\pmod N$. Multiplying gives a square congruent to $52(-143)=-11\cdot26^2$. Since 26 has an inverse modulo $N$, we can cancel $26^2$. The result is $3364^2\equiv-11\pmod N$. This calculation uses only 5,459.

At any odd prime divisor $p$ of $N$, the same square identity holds modulo $p$. Quadratic reciprocity then forces the remainder of $p$ upon division by 11 to be one of **1, 3, 4, 5, 9**. These are exactly the nonzero squares modulo 11. We can jump straight to the five surviving positions in each block of eleven. The prime 13 in the original two remainders disappeared during the multiplication. This is how two individually inconvenient clues can yield one small, repeatable restriction.

In general choose the fixed small support $-1,2,3,5,7,11$. Write each signed remainder as a product of powers of these numbers and a leftover positive cofactor. Group the remainders in every independent way that makes the leftover product a square. For each group the signed product is $D t^2$, with $D$ supported on the chosen small numbers. Each remainder comes with a square root modulo $N$. Multiplying those roots and dividing by $t$ modulo $N$ gives a public square root of $D$. The search checks each such root and tries the usual factor-producing gcd whenever $D=1$. Gaussian elimination over the two-element field constructs a basis of groups, so the search need not visit every subset. Factoring algorithms have long combined partial relations to cancel large primes. We use the surviving small values of $D$ to constrain actual divisors before a square dependency finds a factor. [Lenstra and Manasse, *Factoring with two large primes*](https://doi.org/10.1090/S0025-5718-1994-1250773-9) · [Implementation](../experiments/projected_divisor_wheel.py)

Lean proves that a square root produced this way imposes the positive Jacobi sign on every odd divisor when $D$ is coprime to $N$. It also proves exactly how many small sign patterns the parity equations permit. If $s$ signs are kept and $r$ independent constraints survive elimination, there are $2^{s-r}$ compatible patterns. The count concerns the supplied relations. Forming those relations has a cost, and each allowed pattern can hold for many possible divisors. [Lean proof](../PrimeFactors/SquareClassProjection.lean)

## A factor found before any ordinary square dependency split the input

The first 512 remainders of the 48-bit example produced no single nontrivial clue confined to the chosen small support. Combining remainders produced 22 independent combinations with square leftover product. Of those dimensions, 19 corresponded to ordinary square dependencies. Their gcd tests all missed. The other three yielded these witnesses, which can be checked by squaring and reducing modulo the input.

| Signed remainder $D$ | Square root modulo 246,180,296,426,219 |
|---:|---:|
| −11 | 130,477,127,726,457 |
| 14 | 228,876,284,726,978 |
| 22 | 230,840,503,340,143 |

One can implement the same three restrictions with just **30 positions per 616 integers**. Combining the first and third roots gives a root of −2. Combining that root with the second gives a root of −7. Every odd divisor must therefore lie in one of two classes modulo 8, three classes modulo 7 and five classes modulo 11. Lean checks the numerical roots, containment of every odd divisor and the exact count of 30. The larger test wheel additionally removes multiples of 3 and 5 and leaves 240 positions in every 9,240. On this example the projected divisor search used 6.00 ms of CPU time including the input-specific preparation, against 11.24 ms for plain division. For the sum search, the three clues reduced square tests from 108 to 29, but the preparation raised the time from 0.21 ms to 4.56 ms. [Proof](../PrimeFactors/SquareClassProjection.lean) · [Input, witnesses, exact counts and timings](../research/projected-divisor-wheel.json)

Solving the sign equations before building the list also saves setup. With these five small primes, each complete sign pattern corresponds to 30 wheel positions. Three independent equations leave eight patterns, so the generator builds just 240 positions from 26 local residues. On the same 24 products, building the lists this way took 1.87 ms of CPU in total after 0.011 ms of reusable setup. Checking all 1,920 positions on each product took 14.51 ms after 4.76 ms of setup. Storing all 1,920 positions grouped by sign gave the fastest repeated lookups at 0.44 ms after 4.98 ms of setup. Every method produced exactly the same sorted list. These timings exclude the common cost of finding the roots. [CRT generator and comparison](../experiments/solved_sign_wheel.py) · [Recorded measurements](../research/solved-sign-wheel.json)

## Does the saving hold up on other inputs?

We explored several budgets on the first six products of independent primes at each width. We then fixed 512 remainders and tested the remaining six at each width. All four searches received only the product and the common bit width. The two divisor searches walked upward from the same lower bound. The two sum searches walked upward from the ceiling of $2\sqrt N$, testing whether $s^2-4N$ was a square. All four reused a fixed modulus of 9,240. An ordinary square dependency or a gcd in the setup that already split an input counted as a success with zero further tests.

| Search | Six held-out 20-bit prime pairs | Six held-out 24-bit prime pairs |
|---|---:|---:|
| Divisor search | 86,089 divisions, 8.41 ms | 799,731 divisions, 84.85 ms |
| Divisor search with 512 remainders | 0 divisions after setup, 69.80 ms | 119,311 divisions, 40.19 ms |
| Sum search | 896 square tests, 1.25 ms | 17,602 square tests, 3.60 ms |
| Sum search with 512 remainders | 0 square tests after setup, 69.48 ms | 10,331 square tests, 30.59 ms |

Setup itself recovered all six 20-bit pairs and four of the six 24-bit pairs. Among the two remaining 24-bit products, one yielded no constraint. The other yielded one, halving divisions from 88,309 to 44,154 while leaving the sum search at 2,349 square tests. The time columns are medians across four complete batches on ARM64 Python 3.9.6. One-time reusable tables cost a further 0.35 ms for the unit list, 5.27 ms for the sign list and 1.26 ms for inverses. The ordinary sum search was fastest on both held-out batches. [Reproducible comparison](../experiments/projected_wheel_comparison.py) · [All 24 products](../research/projected-divisor-wheel.json)

## What happened at 2,048 bits?

On both public controls every one of the first 256 remainders had a nonsquare part whose prime factors were absent from the five small primes and the other 255 remainders. Multiplying by any of the other remainders cannot cancel that part. Consequently even trying all $2^{256}-1$ nonempty subsets from this prefix would yield no projected small sign. The benchmark spent 256 ordinary wheel divisions after the failed setup and left each entire product unresolved. Lean regenerates all 256 remainders from each public input and checks a private nonsquare witness for every row. This obstruction describes these particular remainders, multiplier and small support. It does not give a bound on longer prefixes. [Inputs and reproducible budgets](../benchmarks/projected-divisor-wheel.json) · [Full-size Lean certificates](../benchmarks/controls/ProjectedWheelPrivate.lean) · [General obstruction proof](../PrimeFactors/SquareClassPrivateRows.lean)

Run `python3 -m experiments.projected_wheel_comparison --output build/projected-wheel-comparison.json` for the four-way comparison. The regular benchmark includes two complete Lean-checked prime factorizations and both full-size partial results. This experiment uses the project's existing continued-fraction arithmetic and original projection code. The finite calculations use no Riemann hypothesis.
