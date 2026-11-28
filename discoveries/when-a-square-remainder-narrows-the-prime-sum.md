# When a square remainder narrows the prime sum

For $525{,}689$, take the integer square root, 725. The remainder is $525{,}689-725^2=64=8^2$. This tells us enough about the factors to test only midpoints equal to 5 modulo 8. The fifth such test reaches 765 and gives $521\times1009$. Ordinary Fermat takes 40 midpoint tests, and parity alone takes 20. A stronger comparison, screening possible squares modulo 256, takes three exact square tests. With the new rule it takes two midpoint tests plus the one square test on the remainder. [Proof of the rule and control](../PrimeFactors/GaussianSquareRemainder.lean) · [Counted operations](../benchmarks/cyclotomic-root-readings.json)

## Why the square test gives a remainder

For two distinct odd primes, a representation $N=pq=a^2+b^2$ implies both primes are 1 modulo 4. This gives $16\mid(p-1)(q-1)$ and therefore $p+q\equiv N+1\pmod {16}$. If $N\equiv5\pmod8$, one of the two primes is also 1 modulo 8, so the sum is determined modulo 32. A Fermat midpoint is half the sum. This explains the step size of eight or sixteen in the search. The remainder test chooses $a=\lfloor\sqrt N\rfloor$. When the test misses, a different representation may still exist. For example $8{,}249=32^2+85^2$, but $8{,}249-90^2=149$ is between two squares. [Representation and midpoint proofs](../PrimeFactors/GaussianSquareRemainder.lean)

The same information can come from $T_N(i)$, the value of the scaled inverse cyclotomic polynomial at the imaginary unit. A negative imaginary value is equivalent to representability as the sum of two integer squares, and to $-1$ having a square root modulo $N$. The following table gives what can be recovered from the value together with the product. The signs in the last column apply to $N+1$. [Gaussian evaluation and equivalences](../PrimeFactors/CyclotomicGaussianReading.lean) · [Sum congruences and their precision](../PrimeFactors/CyclotomicGaussianPrecision.lean)

| Factors mod 4 | Value at $i$ | Remainder of $p+q$ |
| --- | --- | --- |
| Both 1 | $-2i$ | $+(N+1)$ modulo 16, or modulo 32 for $N\equiv5\pmod8$ |
| Both 3 | $+2i$ | $-(N+1)$ modulo 16, or modulo 32 for $N\equiv5\pmod8$ |
| One of each | $2$ | $N+1$ modulo 8, already determined by the product |

These three, four, or five low bits are sharp in the modular model. Even after specifying the product modulo any positive multiple of 64, two pairs of unit residues can have that same product and Gaussian reading while disagreeing on the next sum bit. The proof of sharpness concerns residues. It does not require every such pair to occur as two primes in a specified size interval. [Precision and explicit residue pairs](../PrimeFactors/CyclotomicGaussianPrecision.lean)

For $N\equiv1\pmod4$, the Jacobi symbol of $-1$ is already $+1$ in both imaginary cases. A two-squares representation gives the additional information that this particular product actually has a square root of $-1$. [Earlier connection between square existence and the sum](one-modulus-and-the-low-bits-of-the-prime-sum.md)

The 14-bit products $9{,}017=71\cdot127$ and $8{,}249=73\cdot113$ share all eight low product bits. Their Gaussian readings are $+2i$ and $-2i$ and their sums are 6 and 10 modulo 16. We constructed the polynomials using the indices alone for these controls. The coefficient construction visits both factors. A positive square-remainder test supplies the negative imaginary value without that construction. [Exact arithmetic and independent factor checks](../experiments/cyclotomic_root_readings.py)

## What the search saved

We enumerated every unordered pair of distinct primes of the stated bit width whose product has twice that width. Each search starts from the product and runs to its first verified factorization. Before paying for the extra square test, the new rule checks the product modulo 4 and tests whether the remainder can be a square modulo 256, 3, 5, 7 and 11 in that order. After a miss it resumes the baseline. All gate square tests count, including failures. Positive savings mean fewer exact square tests across the complete population; negative values mean more. [Procedure and fixture](../experiments/cyclotomic_root_readings.py) · [Operation counts](../benchmarks/cyclotomic-root-readings.json)

| Bits per prime | Eligible products | Pass the square test | Savings against parity | Savings against a modulo-256 midpoint screen |
| ---: | ---: | ---: | ---: | ---: |
| 9 | 543 | 16 | −5 | −19 |
| 10 | 1,718 | 50 | 120 | −54 |
| 11 | 5,530 | 94 | 446 | −109 |
| 12 | 19,546 | 276 | 3,004 | −226 |
| 13 | 64,719 | 716 | 15,148 | −131 |
| 14 | 228,713 | 1,704 | 75,409 | 2,675 |

The last row was evaluated with the rules fixed from the smaller cases. The modulo-256 baseline took 4,681,605 exact square tests. The new search took 4,672,338 midpoint square tests and 6,592 gate square tests, a net reduction of 0.0571%. The midpoint scan also avoided 82,001 modulo-256 lookups, while the gate added 445,055 residue lookups. That leaves 363,054 additional small lookups. These measurements compare operations and do not establish a time saving. Reproduce the last row with `python3 -m experiments.cyclotomic_root_readings --gate-width-14`.

## How often the square test can work at full size

Lean proves that fewer than one in $2^{487}$ eligible pairs of 1,024-bit primes passes the floor-square-root remainder test. The next square is only $2\lfloor\sqrt N\rfloor+1$ away, so if the remainder is a square its root is less than $2^{513}$. For each possible small coordinate the other coordinate has a bounded range and a fixed parity. Each choice gives just one product. A separate upper bound covers trying a fixed list of up to $2^{40}$ coordinates, each at most $2^{513}$: fewer than one in $2^{960}$ pairs has a representation using that list. Both bounds count all distinct eligible pairs with 2,048-bit products and require no external prime-distribution assumption. [Single-test population proof](../PrimeFactors/GaussianSquareRemainder.lean) · [Coordinate counts and the list bound](../PrimeFactors/GaussianSquareMenu.lean)

A particularly cheap positive test occurs when $N=t^2+1$. The first Fermat midpoint is $t+1$ and the sequence that tests every fourth midpoint starting there includes the true midpoint. At $698{,}897=836^2+1$ this gives four midpoint tests instead of thirteen consecutive tests or seven odd-midpoint tests. The full modulo-16 sum rule retains just 841 and 849. On this example a direct modulo-256 screen already retains only 849 from the odd midpoints before success. [Stride proof and adjacent-square control](../PrimeFactors/GaussianSquareMenu.lean)
