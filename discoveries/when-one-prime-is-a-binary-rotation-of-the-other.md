# When one prime is a binary rotation of the other

The binary words for 47 and 59 are `101111` and `111011`. Moving the first four bits of 47 to the end gives 59. Their product, 2,773, already tells us that any matching shift must be even. The product 2,419 passes the same kind of modular square test, yet none of the rotations of 41 gives its other prime factor, 59. [Both orientations of the first example](../PrimeFactors/BinaryRotationProduct.lean) · [False-positive example](../PrimeFactors/FullWidthRotationRoots.lean)

## What the product tells us

For a word of width $w$, let $M=2^w-1$. Moving the leftmost $j$ bits to the right in the same order multiplies the word by $2^j$ modulo $M$. If the factors $p$ and $q$ are related by that rotation, then

$$ (2^{\lceil j/2\rceil}p)^2 \equiv 2^{j\bmod 2}N \pmod M. $$

For even $w$, three divides $M$. For primes larger than three, a nonzero square is one modulo three, so $N\bmod 3$ determines the shift parity. Remainder one gives an even shift and remainder two gives an odd shift. At width 1,024 this leaves 511 even or 512 odd nonzero shifts. The modular square test for the opposite parity has no solutions. At odd widths, adding a full rotation to an odd shift allows the use of $N$ itself for both parities. [Rotation identities and small examples](../PrimeFactors/BinaryRotationProduct.lean) · [Parity and shift counts](../PrimeFactors/BinaryRotationPopulation.lean)

## What it means to pass the square test

At width 1,024, the public constant $M=2^{1024}-1$ has exactly 16 distinct prime factors, each occurring once. Every 1,024-bit prime is larger than all sixteen. For a product of two such primes, a modular square test at $M$ has either zero roots or exactly **65,536**. A represented unit has two roots at each prime, and the Chinese remainder theorem gives independent choices at all sixteen. The previously certified example with two 512-bit blocks has all 65,536 roots in its even class. The count describes possible residues and supplies no elapsed-time measurement. [Kernel-checked factorization of the constant](../PrimeFactors/BinaryRotationModulus.lean) · [Root count over a squarefree modulus](../PrimeFactors/RotationSquareRootCount.lean) · [Full-width count and planted example](../PrimeFactors/FullWidthRotationRoots.lean)

The six-bit false positive illustrates what can survive. The numbers 5, 23, 40 and 58 all square to $2419\bmod 63$. The complete rotation check returns no pair. At the same width, $2279=43\cdot53$ shows the odd-shift case. Here the square to test is $2N\bmod63$. [Exact positive and negative controls](../PrimeFactors/FullWidthRotationRoots.lean) · [Odd-shift control](../PrimeFactors/BinaryRotationProduct.lean)

The complete six-bit census has 14 unordered pairs of distinct primes with a 12-bit product. Six pass a root test. Four really are rotations, and two are false positives, $41\cdot59=2419$ and $41\cdot61=2501$. Each shift parity therefore admits a false positive in this small population. [All fourteen products and the exact passing lists](../PrimeFactors/SmallRotationCensus.lean)

Over all residues coprime to $M=2^{1024}-1$, **exactly one in 32,768** passes either square test. Each represented unit has 65,536 square roots, so the squares make up one in 65,536 of the units. Doubling permutes the units, and the two passing sets are disjoint modulo three. This denominator counts every coprime residue in one full period with equal weight. The next bound counts actual prime pairs. [Finite count for both square classes](../PrimeFactors/RotationSquareClassDensity.lean)

## How often do the prime factors have this relation?

Among all unordered pairs of distinct 1,024-bit primes with a 2,048-bit product, **fewer than one in $2^{998}$** pairs admit even one nonzero rotation. Once one prime is fixed it has only 1,023 possible nonzero shifts, and every qualifying pair is counted in both directions. Lean compares that count with a lower bound on the size of the full prime-pair population. The bound allows a different shift for every product. [Unconditional population bound](../PrimeFactors/BinaryRotationPopulation.lean)
