# When the actual interval separates factor sums

For $N=7{,}294{,}033$, knowing that both prime factors have 12 bits gives 52 possible positions for their sum. Testing sums modulo 63 leaves four. A radix-eight digit distinguishes all four in this particular interval. Move the interval just one position and two of the survivors share a digit. Adding the test modulo five to the original window leaves a single sum even without a digit. [Lean proof of the worked example](../PrimeFactors/FixedWindowDigitPacking.lean)

For the two 2,048-bit comparison products, using the actual starting position saved **zero bits** of the supplied cyclotomic evaluation for each of the three tested moduli. The factor widths are public, and the calculation uses no factor values. [Exact results](../research/fixed-window-digit-packing.json)

## What the minimum measures

Let $N=pq$ for distinct odd primes, and let $S=p+q$. From $N$ we know that $W$ divides $F=(p-1)(q-1)=N+1-S$, where $W$ is 4, 8, 12 or 24. Write $g=W/2$. The public width bounds give consecutive possible indices $x=a+i$, with $0\le i<C$, and a proposed sum $S=N+1-Wx$ at each index. A local test with modulus $m$ keeps $S$ when two residues modulo $m$ have product $N$ and sum $S$. Every true sum passes. [Forced stride and index bounds](../PrimeFactors/CyclotomicRadixLift.lean)

For a radix $M\ge1$, the digit is $gx\bmod M$. The cyclotomic evaluation $\Phi_N(1+M)\bmod M^2$ supplies this digit. The **least separating radix** is the smallest positive $M$ for which every surviving index in the specified window has a different digit. The comparator uses the same modulus, length, stride and product residues and requires one radix to work at *every* starting position. In either case a correct digit must be supplied to select among several sums. The calculation below finds the radix without evaluating the polynomial. [Cyclotomic identity](../PrimeFactors/CyclotomicSumDigit.lean)

## The four surviving sums

For the small product, the forced stride is 4 and the first index is 1,822,107. The exact survivors modulo 63 are as follows.

| Offset from the first index | Candidate sum | Digit at radix 8 |
|---:|---:|---:|
| 7 | 5,578 | 4 |
| 24 | 5,510 | 6 |
| 33 | 5,474 | 0 |
| 42 | 5,438 | 2 |

Lean checks a collision for every smaller positive radix. Requiring all starting positions would raise the minimum to 16. With modulus 315 only offset 33 survives in the original window. The resulting sum 5,474 gives the certified primes 2,293 and 3,181. The reproduction builds the local table from the product, width and modulus, takes the square root of the discriminant at the sole surviving sum, then compares the recovered factors with the fixture. Lean checks their primality independently. [Worked fixture](../benchmarks/fixed-window-digit-packing.json) · [Window and primality proofs](../PrimeFactors/FixedWindowDigitPacking.lean) · [All-phase comparison](../research/fixed-window-digit-packing.json)

That single square test follows a setup calculation. The width interval needs one integer square root and two divisions to bound the sum. Constructing the table visits 315 residues and takes 315 gcds, plus one gcd to obtain the table period. Of the residues, 144 are invertible and yield 144 ordered pairs after one modular inversion apiece. Their sums occupy 12 distinct entries. The search builds all 315 entries, counts the entries for the actual 52 positions, and reads through offset 33 to locate the survivor. For comparison, ordinary Fermat starts at midpoint 2,701 and reaches 2,737 on its 37th square test. [Measured benchmark method](../experiments/fixed_window_digit_packing.py)

## Computing across a long interval

The local test repeats every $T=m/\gcd(m,W)$ indices. Two indices share a digit exactly when their difference is a multiple of $P=M/\gcd(M,g)$. To test a proposed radix, it suffices to check offsets $0\le i<T$ and displacements $hP$ with $1\le h\le T/\gcd(T,P)$. A collision occurs if both offsets survive and $i+hP<C$. The strict inequality includes the last valid index and excludes the first position past the window. [Finite collision criterion](../PrimeFactors/FixedWindowDigitPacking.lean)

To minimize $M$ we first tabulate, for each displacement residue $j\bmod T$, the earliest starting offset $i<T$ at which both ends pass. Empty entries impose no restriction. Once $v=P\bmod T$ is fixed, every recorded pair for $j=hv\bmod T$ requires $P\ge\lceil(C-i)/h\rceil$. The largest such bound is the exact cutoff for that phase. Stepping $M$ by $gT$ preserves the phase and increases $P$ linearly. This leaves $gT$ arithmetic progressions of radices, with one rounding operation per progression to find its first adequate radix. [Threshold and monotonicity proofs](../PrimeFactors/FixedWindowDigitPacking.lean)

The implementation builds the modular table by solving $xy=N\bmod m$ for each residue $x$. After that table, computing the minimum takes $O(T^2+gT)$ arithmetic operations and $O(T)$ storage. The integers in the endpoint arithmetic grow with the bit length of $C$. A separate check looks for a collision at the claimed minimum and exhibits one for the last smaller radix in every progression that contains one. This verifies minimality without iterating over the $C$ indices or all $M$ below the answer. A direct survivor-list calculation agrees in 3,048 bounded cases. [Reproduction script](../experiments/fixed_window_digit_packing.py)

## The 2,048-bit controls

The figures count bits needed to represent a residue modulo $M^2$, namely the bit length of $M^2-1$. Both factors are promised to have 1,024 bits. The uniform column uses the same local test at every possible starting position.

| Public product | Modulus | Actual-window bits | All-starts bits | Reduction in the minimum radix |
|---|---:|---:|---:|---:|
| Fresh | 35 | 2,028 | 2,028 | 0 |
| Fresh | 63 | 2,024 | 2,024 | 0 |
| Fresh | 315 | 2,024 | 2,024 | 0 |
| Crossed | 35 | 2,036 | 2,036 | 10 |
| Crossed | 63 | 2,032 | 2,032 | 0 |
| Crossed | 315 | 2,032 | 2,032 | 0 |

The fixed-window theorem gives a reason the gain can be small when $T$ is small. Set $K=20160/\gcd(20160,WP)$. At every starting position, a locally admissible pair separated by $PK$ can be aligned with the first $T$ indices. Consequently a separating radix requires $C\le PK+T-1$. This constrains reconstruction by one digit and the chosen modular table. Other sources of information about the factors fall outside this bound. [Actual-window bound](../PrimeFactors/FixedWindowDigitPacking.lean)

The general criterion and small worked example are kernel-checked in Lean. For each full-size entry, an independent Python check verifies both minima. For the all-starts comparison it enumerates ordered residue pairs directly, verifies separation at the winning radix and finds a colliding pair with a specific starting phase for each smaller radix progression. For modulus 315, each minimum had 1,260 such losing progressions on the fresh product and 630 on the crossed product. The computation uses only the decimal product and declared factor width from the existing fixture. Neither full-size digit was obtained and neither product was factored by this calculation. Run the following commands at the repository root. [Input fixture](../benchmarks/intermediate-totient-rows.json) · [Exact radices, survivor counts and witness counts](../research/fixed-window-digit-packing.json)

```sh
lake build PrimeFactors.FixedWindowDigitPacking
python3 -m experiments.fixed_window_digit_packing --check
python3 -m unittest discover -s tests -p test_fixed_window_digit_packing.py
```
