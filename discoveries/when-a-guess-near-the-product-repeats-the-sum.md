# When a guess near the product repeats the factor sum

One way to choose a number for the continued-fraction search is to subtract a guessed offset from the product. For a 2,048-bit product of two distinct 1,024-bit primes, Lean proves that every offset from zero to $2^{1535}$ gives the same answer as testing the proposed prime sum directly. The only successful offset in that entire range is $p+q-1$. Given the offset $k$, one can test whether $(k+1)^2-4N$ is a nonnegative perfect square and verify the resulting pair. Going through continued fractions adds no information to this test. [Theorem and assumptions](../PrimeFactors/PowerRatioAnchor.lean)

A different way to choose a guess is to multiply the product by a simple fraction and round down. Every choice $E=\lfloor cN/d\rfloor$ with $1\le c\le d\le 2^{509}$ misses the true ratio among the ordinary continued fractions of $E/N$. This holds even if we inspect the product before choosing the fraction.

## What forces a single answer?

Write $F=(p-1)(q-1)$ and $D=N-F$. The prime widths give $2^{1024}\le D\le 2^{1025}$. If a guess $E$ succeeds, its greatest common divisor $g$ with $F$ satisfies $EFD<Ng^2$. Since both $dE$ and $cF$ are multiples of $g$, a distance smaller than $g$ forces equality. The endpoints of the public interval for $D$ bound that distance without either prime. Under the additional short-fraction condition in the theorem, equality also guarantees that the ratio occurs. [Gcd bound](../PrimeFactors/ConvergentGcdThreshold.lean) · [Interval proof](../PrimeFactors/PowerRatioAnchor.lean)

The size condition matters. For $437=19\times23$, the guess $E=437-173=264$ produces the ratio $2/3$ and the prime sum 42. The true offset is 41. We chose this small example to show where the implication can fail. The benchmark receives 437, the common prime width and 264. Lean checks the recovered primes. [Benchmark fixture](../benchmarks/power-ratio-remainder.json)
