# Reading the other fourth power

Given **2,126,389**, divide by four and take the integer fourth root to get 27. Subtract $4\times27^4$ from the original input to get 625, whose fourth root is 5. Sophie Germain’s identity then gives **1,213 × 1,753**, both prime. Starting with the fourth root of $N$ would give 38 and miss. On the earlier example 151,847,041, starting with $N$ works and starting with $N/4$ misses. [Lean proofs of both examples](../PrimeFactors/ComplementaryQuarticProducts.lean) · [Original recognizer](two-fourth-roots-reveal-a-special-factor-pair.md)

The two directions recover positive representations $N=x^4+4y^4$ under different conditions. Starting with $N$ recovers $x$ when $N<(x+1)^4$. Starting with $\lfloor N/4\rfloor$ recovers $y$ when $N<4(y+1)^4$. Each branch checks the exact equation. Evaluating both uses four integer fourth roots, each implemented as two integer square roots. [Recognition and exact coverage of the two branches](../PrimeFactors/ComplementaryQuarticProducts.lean)

**Every success of the second branch is an additional success on balanced odd semiprimes**, where balanced here means $p\le q\le2p$. Prime factorization fixes the returned ordered pair, which in turn fixes the positive coordinates $x,y$. For odd products the only coordinates meeting both size conditions give 5, 145 and 949. None is a balanced odd semiprime. Composite inputs with more than two prime factors can behave differently. For example, from 7,585 the branches return $41\times185$ and $37\times205$, two different pairs. [Uniqueness, exact small exceptions and composite example](../PrimeFactors/ComplementaryQuarticProducts.lean)

| Odd inputs through | First branch only | Second branch only | Both | Eligible prime pairs from first branch | Additional eligible pairs from second |
| --- | ---: | ---: | ---: | ---: | ---: |
| $2^{16}$ | 31 | 39 | 4 | 0 | 1 |
| $2^{24}$ | 399 | 455 | 4 | 2 | 5 |
| $2^{32}$ | 4,630 | 5,117 | 6 | 30 | 49 |

The last two columns require two $b$-bit primes whose product has $2b$ bits. The complete census through $2^{32}$ thus rises from **30 to 79** eligible prime pairs. Up through $2^{16}$ the check also scans every odd integer independently. [Reproduce the census](../experiments/complementary_quartic_strips.py)

For two 1,024-bit primes with a 2,048-bit product, the first branch can cover at most $24\cdot2^{888}$ products and the second at most $25\cdot2^{888}$. Together their share of eligible products is **less than one in $2^{1128}$**. These unconditional bounds include every candidate parameter choice, even choices that would return composite factors. They give no lower bound on the number of full-size semiprimes represented. [Both upper bounds and exact disjointness on the target population](../PrimeFactors/ComplementaryQuarticPopulation.lean)
