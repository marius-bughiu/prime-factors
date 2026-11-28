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

The last row was evaluated with the rules fixed from the smaller cases. The modulo-256 baseline took 4,681,605 exact square tests. The new search took 4,672,338 midpoint square tests and 6,592 gate square tests, a net reduction of 0.0571%. The midpoint scan also avoided 82,001 modulo-256 lookups, while the gate added 445,055 residue lookups. That leaves 363,054 additional small lookups. Reproduce the counts with `python3 -m experiments.cyclotomic_root_readings --gate-width-14`.

We also timed both searches on the same 228,713 products. The new rule took longer in all five paired trials on CPython 3.9.6, Darwin arm64. Median elapsed time for one pass through the cohort was 0.909 seconds for the modulo-256 baseline and 0.931 seconds with the rule. The paired increases ranged from 1.49% to 3.64%, with a median of 2.49%. Median process CPU time rose from 0.904 to 0.927 seconds. Each policy had a full warmup, and we alternated which ran first. The timers included candidate generation, residue lookups and square tests. We generated the input products and checked the factor labels and reference counts beforehand. These timings apply to this implementation, interpreter and 28-bit population. Reproduce them with `python3 -m experiments.time_gaussian_square_gate --trials 5`. [Optional timing harness](../experiments/time_gaussian_square_gate.py)

| Trial (first policy timed) | Elapsed seconds, baseline / rule | CPU seconds, baseline / rule |
| --- | ---: | ---: |
| 1 (baseline) | 0.9086 / 0.9417 | 0.9042 / 0.9349 |
| 2 (rule) | 0.9039 / 0.9295 | 0.9008 / 0.9266 |
| 3 (baseline) | 0.9034 / 0.9255 | 0.9020 / 0.9244 |
| 4 (rule) | 0.9174 / 0.9310 | 0.9121 / 0.9264 |
| 5 (baseline) | 0.9107 / 0.9334 | 0.9086 / 0.9294 |

### Why the stronger strides give the same exact tests

After the gate succeeds, midpoints $m$ in the step-four search satisfy $m\equiv(N+1)/2\pmod4$. If $N\equiv1\pmod8$, testing whether $m^2-N$ is a square modulo 16 already forces $m\equiv(N+1)/2\pmod8$. If $N\equiv5\pmod8$, the square test modulo 32 forces the corresponding midpoint class modulo 16. A modulo-256 square must pass both smaller square tests. Thus starting with stride four and applying the modulo-256 screen sends exactly the same midpoints to the exact square test as starting with the stronger stride of eight or sixteen and applying that screen. The stronger stride skips residue lookups on the way. [Lean equivalence](../PrimeFactors/GaussianMidpointScreen.lean)

The next smaller screen can admit a wrong midpoint on each branch. For $525{,}689=521\cdot1009$, $m=729$ is in the step-four class. Its difference is 5,752, a square modulo 8, while the midpoint is 1 modulo 8 and the required residue is 5. For $133{,}901=293\cdot457$, $m=367$ gives a difference of 788, a square modulo 16. The midpoint is 15 modulo 16 and the required residue is 7. Both products pass the remainder gate. The true midpoints are 765 and 375. [Checked witnesses](../PrimeFactors/GaussianMidpointScreen.lean)

## How often the square test can work at full size

Lean proves that fewer than one in $2^{487}$ eligible pairs of 1,024-bit primes passes the floor-square-root remainder test. The next square is only $2\lfloor\sqrt N\rfloor+1$ away, so if the remainder is a square its root is less than $2^{513}$. For each possible small coordinate the other coordinate has a bounded range and a fixed parity. Each choice gives just one product. A separate upper bound covers trying a fixed list of up to $2^{40}$ coordinates, each at most $2^{513}$: fewer than one in $2^{960}$ pairs has a representation using that list. Both bounds count all distinct eligible pairs with 2,048-bit products and require no external prime-distribution assumption. [Single-test population proof](../PrimeFactors/GaussianSquareRemainder.lean) · [Coordinate counts and the list bound](../PrimeFactors/GaussianSquareMenu.lean)

A particularly cheap positive test occurs when $N=t^2+1$. The first Fermat midpoint is $t+1$ and the sequence that tests every fourth midpoint starting there includes the true midpoint. At $698{,}897=836^2+1$ this gives four midpoint tests instead of thirteen consecutive tests or seven odd-midpoint tests. The full modulo-16 sum rule retains just 841 and 849. On this example a direct modulo-256 screen already retains only 849 from the odd midpoints before success. [Stride proof and adjacent-square control](../PrimeFactors/GaussianSquareMenu.lean)

## How much of the full search could the shortcut save?

Imagine knowing for free which products pass the square-remainder test and receiving their factors for free too. Even then the saving is **less than one part in $2^{439}$** of all exact square tests that the parity- and modulo-256-screened Fermat scan would perform over the full population. This measures work across all distinct pairs of 1,024-bit primes with 2,048-bit product, giving each pair one run. The bound allows successes to occur disproportionately on expensive inputs. [Aggregate work theorem](../PrimeFactors/GaussianGateAggregateCost.lean)

To see why, write $m=(p+q)/2$ for the true midpoint. More than two thirds of eligible pairs have a gap of at least $2^{1006}$. On each such pair the $2^{977}$ midpoints $m-256i$ for $0\le i<2^{977}$ are all at or above the first Fermat midpoint. They have the same parity and the same square residue modulo 256 as $m$, so the baseline must test every one. Each individual search makes at most $2^{1024}$ exact tests. Combining these two work bounds with the rarity of positive square remainders gives the result without extrapolating from the small timing experiment. [Large-gap population](../PrimeFactors/SeparatedMonotonePopulation.lean) · [Midpoints and cost comparison](../PrimeFactors/GaussianGateAggregateCost.lean)
