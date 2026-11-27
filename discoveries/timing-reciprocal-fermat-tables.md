# Do reusable factor-sum tables make a blind search faster?

All three searches recovered all 24 independently generated prime pairs. The new Jacobi rule roughly halved the number of exact square tests already left by the ordinary modular sieve. At both sizes, building and sorting tables took more CPU time in total than the simple modulus-60 search. The new rule did produce individual end-to-end wins. On one 48-bit product, its selected modulus was just 47 and it found the factors in 1.34 ms, compared with 2.43 ms for the ordinary table and 5.20 ms for modulus 60 alone. [Per-product counts, outcomes and all six timings](../research/reciprocal-fermat-holdout.json)

| Bits per prime | Method | Exact square tests through first split, all 12 inputs | Median CPU time for all 12 | Median elapsed time for all 12 |
|---|---|---:|---:|---:|
| 20 | Modulo 60 | 7,812 | 1.52 ms | 1.53 ms |
| 20 | Ordinary table + modulo 60 | 3,802 | 20.52 ms | 20.53 ms |
| 20 | Oriented table + modulo 60 | 1,891 | 28.93 ms | 28.95 ms |
| 24 | Modulo 60 | 192,730 | 34.12 ms | 34.14 ms |
| 24 | Ordinary table + modulo 60 | 68,806 | 179.37 ms | 179.55 ms |
| 24 | Oriented table + modulo 60 | 34,336 | 315.09 ms | 315.35 ms |

For each width we took the first 12 distinct-prime pairs from separate SHAKE256 streams for the two factors and retained every product. The seed was `reciprocal-fermat-holdout-v1/20` or `reciprocal-fermat-holdout-v1/24`. Both width groups included ten products of twice the factor width and two that were one bit shorter. Search used the product and the common factor width. The generated primes were used afterward to check the returned factors. [Input generator](../experiments/affine_radix_holdout.py) · [Complete experiment](../experiments/reciprocal_fermat_holdout.py)

## What each search counted

All three methods scanned candidate sums in ascending order. Let $U=2^b$, where $b$ is the known factor width, and $x_0=\max(U/2,\lceil N/(U-1)\rceil)$. The smaller factor lies between $x_0$ and $\sqrt N$. Its sum with its partner therefore lies between $\lceil2\sqrt N\rceil$ and $x_0+\lfloor N/x_0\rfloor$. Each search started with the same admissible sum residues modulo 60. At each surviving sum $s$ it tested whether $s^2-4N$ is an integer square, checked the product of the resulting pair and stopped at the first split.

Both table methods paid for 256 continued-fraction steps per input. Each chose the shortest eligible modulus $d$ found by the existing public rule. The predeclared fallback was to continue with modulus 60 if the search found no eligible period or if $d>1{,}000{,}000$. A proper gcd during setup would count as a factorization. Every input in this panel yielded an eligible period under the cap and reached the square-test stage. [Anchor rule and its two square certificates](../experiments/reciprocal_anchor.py)

The ordinary method tabulated the squares modulo $d$ using representatives $0$ through $\lfloor d/2\rfloor$. It checked $s^2-4N$ against that table for every $s$ modulo $d$. The oriented method built the same table, then evaluated the Jacobi rule once per pair of opposite ordinary sum residues to select one of them. Each method combined its classes with the modulus-60 classes using CRT and sorted the combined residues. The scan reused that list throughout the interval with no Jacobi evaluation per visited sum. [Lean proof of the selector and its cardinality](../PrimeFactors/OrientedTraceClasses.lean) · [Interval bounds for the two tests](../PrimeFactors/HalfPeriodWindow.lean)

## Where the time went

For the twelve 24-bit pairs, orientation reduced the number of CRT rows from **572,592 to 286,296**. Median CPU time for constructing and sorting these rows fell from 75.05 to 37.26 ms, and scanning to the first split fell from 9.97 to 4.99 ms. Building the underlying square table took about 89 ms for each method. Evaluating the 118,526 canonical tags added 179.36 ms. For the 20-bit group there were 12,776 tag evaluations and 53,698 oriented CRT rows.

Period size mattered. On $163433502902129=10330367\cdot15820687$, $d=47$. The modulus-60, ordinary and oriented searches needed 29,142, 14,884 and 7,443 square tests respectively. On $145002691065893=9004531\cdot16103303$, $d=636907$. Orientation reduced 8,537 ordinary square tests to 4,222, yet CPU time grew from 100.52 to 202.13 ms. Modulus 60 alone took 6.70 ms on that input. On a per-product median basis, three of the twelve oriented 24-bit searches and none of the twelve oriented 20-bit searches beat modulus 60. Those observations depend on this panel, interpreter and hardware. They provide no runtime estimate at 2,048 bits.

The recorded timings use Python 3.9.6 on ARM64 macOS. Six repetitions rotate through all six orders of the three methods for each product. Every call rebuilds that product's tables. Timers around the entire search include setup, sorting, scanning and table disposal. Input generation, correctness checks against the held-out primes and Lean verification are outside the timers. The stored counts and timing samples are sufficient to recompute each sum and median. [Machine details and raw timings](../research/reciprocal-fermat-holdout.json)

## Reproduce and verify

From the repository root, run `python3 -m experiments.reciprocal_fermat_holdout --verify-report research/reciprocal-fermat-holdout.json` to regenerate and check the aggregate Lean certificate. It proves one conjunction of 24 `ExactFactorization` statements, including primality of both factors in every pair. Its source SHA-256 is `d34d33b391e33513be62f550922007507121cd3aa5070e9f20943d03f5d9ae01`. To regenerate the inputs, time all three methods and recheck the results, run `python3 -m experiments.reciprocal_fermat_holdout --output build/reciprocal-fermat-rerun.json`. [Certificate generator and search driver](../experiments/reciprocal_fermat_holdout.py)
