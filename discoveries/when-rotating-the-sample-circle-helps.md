# When rotating the sample circle helps

For $323$, changing where 42 equally spaced measurements start lets us recover the prime sum $36$. Every ordinary grid with up to 84 points includes an earlier coefficient large enough to spoil direct rounding. An ordinary grid with one explicit subtraction also recovers $36$ using the same 42 evaluations and much less preparation. Ordinary Fermat search sees $18^2-323=1$ and recovers $17\times19$ in one square test. [Experiment](../experiments/rotated_coefficient_filter.py)

## Why the angle matters

Take the series whose coefficient $a(n)$ sums the divisors $d$ of $n$ for which both $d$ and $n/d$ exceed 3. At a product of two distinct primes above 3, this coefficient is their sum. An ordinary grid of $M$ points retains positions $N$, $N\pm M$, $N\pm2M$, and so on. Rotating the grid by $\theta$ and taking the real part multiplies the contribution from $N\pm jM$ by $\cos(jM\theta)$. With $\theta=\pi/(2^{v+1}M)$, that multiplier vanishes exactly when $j$ is an odd multiple of $2^v$. Lean proves the finite sampling identity and this cancellation rule. The identity extends to the infinite series at radius $0<r<1$ by absolute convergence. [Lean proof](../PrimeFactors/RotatedCoefficientFilter.lean) · [Ordinary sampling and normalization](reading-a-factor-sum-from-equally-spaced-samples.md)

At $N=323$ and $M=42$, the earlier positive positions are $281,239,197,155,113,71,29$. Only $155=5\times31$ contributes. It lies four steps back, so starting at $\pi/336$ gives it weight $\cos(\pi/2)=0$. The coefficient at $323$ retains weight one. The rotated rule found this phase using only the product. It tried 204 grid-and-angle choices, checked 442 step indices, and used 91 integer square roots and 637 trial divisions to test earlier coefficients. [Checked earlier positions](../PrimeFactors/RotatedCoefficientFilter.lean) · [Search and work counters](../experiments/rotated_coefficient_filter.py)

The ordinary comparison used 83 points. Its complex conjugate pairs share an evaluation, leaving 42 actual evaluations. Its three earlier positions are $240,157,74$. Only $a(240)=298$ contributes. Computing the correction took three integer square roots, 26 trial divisions and one shifted addition. At radius $1/2$, exact evaluation and a bound on the infinite tail placed the two answers within $2.67\times10^{-11}$ and $1.35\times10^{-23}$ of 36 for the rotated and corrected grids respectively. [Exact arithmetic](../experiments/rotated_coefficient_filter.py)

## All 109 products

The panel includes every product of two distinct primes of the same width at 5, 6 and 7 bits. The search tries $M=1,\ldots,64$ and increasing $v$, stopping once every earlier coefficient with a nonzero cosine is provably zero. It recovered six of the ten 5-bit cases, zero of 21 at 6 bits, and zero of 78 at 7 bits. For each success the ordinary comparison used $2M-1$ points, the same $M$ evaluations, and separately subtracted its earlier contributions. [Expected factors](../benchmarks/rotated-coefficient-filter.json) · [Lean product and primality checks](../PrimeFactors/RotatedCoefficientFilter.lean)

| Product | Factors recovered by both rules | Evaluations per rule | Rotated trial divisions | Corrected ordinary trial divisions |
| ---: | ---: | ---: | ---: | ---: |
| 323 | 17 × 19 | 42 | 637 | 26 |
| 391 | 17 × 23 | 35 | 603 | 46 |
| 437 | 19 × 23 | 50 | 827 | 38 |
| 493 | 17 × 29 | 50 | 866 | 47 |
| 527 | 17 × 31 | 55 | 963 | 48 |
| 551 | 19 × 29 | 60 | 1,049 | 46 |

Five of the six rotations use $v=0$. By conjugacy, these give the real part of the ordinary average on a finer grid of $2M$ points offset by half a step. Only $323$ defeated every uncorrected, unrotated grid up to $2M$ points. Once earlier coefficients were priced, the corrected rule needed fewer divisor tests and fewer integer square roots on all six products. [Complete comparison](../experiments/rotated_coefficient_filter.py)

Run `python3 -m experiments.rotated_coefficient_filter` to reproduce the panel. The Python checker evaluates each distinct sample exactly through degree $N+96$ and bounds the rest using $a(n)\le n^2$. At 323 each rule evaluates 420 terms at each of 42 points. This validation computes the coefficient list through the target itself. Efficient access to equivalent samples on large inputs remains open. [Checker](../experiments/rotated_coefficient_filter.py)
