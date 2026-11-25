# A wider test using three small primes

Dividing the input by 3, 5 and 7 tells us something about *every* unknown factor. If none divides the input, none divides a factor either. We used this information to build a seven-coefficient equation that checks a whole interval at once. On **132,079**, the equation found **269**, and Lean certified the complete split **269 × 491**. On two 2,048-bit inputs, Lean certified wider intervals empty. Finding which interval contains a prime remains open. [Small example](https://marius-bughiu.github.io/prime-factors/#sifted-divisor-window-132079-16) · [Lean proofs](../PrimeFactors/SiftedDivisorWindow.lean)

## What the product lets us discard

Write a proposed odd divisor as $d=c+2x$, where the odd center $c$ is public. Pick the representative $s$ of $c/2$ modulo 105 between $-52$ and 52. If $N$ is coprime to 105, then each divisor corresponds to a position where $z=x+s$ is coprime to 105. This leaves 48 of the 105 residue classes. We keep a single equation for their union. The executable checks a gcd with the full clearing denominator up front. A proper common divisor already splits the input. [Eligibility and cancellation](../PrimeFactors/SiftedDivisorWindow.lean) · [Search implementation](../experiments/binomial_divisor_window.py)

Choose the six nodes $-16,-17,-19,22,-11,-22$. Let $P_i(z)$ be the product of $z$ minus the first $i$ nodes, including $P_0=1$. At every allowed position $P_i(z)/D_i$ is an integer. The denominators for degrees zero through six are:

| Degree | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Consecutive integer positions, $i!$ | 1 | 1 | 2 | 6 | 24 | 120 | 720 |
| Positions allowed by 3, 5 and 7, $D_i$ | 1 | 1 | 6 | 6 | 360 | 360 | 45,360 |

For instance, every allowed $z$ falls in one of the two nonzero classes modulo 3. The first two nodes occupy these two classes and have opposite parity. Their product of differences is therefore divisible by six. Lean checks every degree by prime powers. It also proves that six eligible test arguments already have gcd exactly $D_i$ in each row, so no larger denominator divides every allowed value of that row. The product of the seven denominators increases by a factor of 8,505. The actual window gain also depends on the size of the numerators. This applies the earlier calculation for factor remainders to offsets in an ordinary divisor interval. [Earlier unit-node construction](unit-newton-lanes.md) · [Bhargava on integer-valued polynomials](https://doi.org/10.1515/crll.1997.490.101)

## How an equation rules out a range

Use the seven polynomials $P_i(x+s)/D_i$ as coordinates. Multiplication by 45,360 clears every denominator. At a true divisor $d$ in the interval the resulting polynomial value is both a multiple of $d^3$ by the Taylor conditions and 45,360 times an integer by the unit tests. Since $d$ is coprime to 45,360, that integer is divisible by $d^3$. A strict upper bound smaller than $d^3$ forces zero. A nonzero polynomial of degree at most six leaves at most six integer roots to check. A modulus with no root excludes the whole interval. [Certificate theorem and finite existence proof](../PrimeFactors/SiftedDivisorWindow.lean) · [Taylor conditions](../PrimeFactors/HigherDivisorWindow.lean)

For any odd center, the finite existence proof guarantees an equation with $|x|\le 13\cdot2^{435}$ for a divisor at least $2^{1023}$ of an odd input at most $2^{2048}$ coprime to 45,360. Here the radius is in odd positions, so the interval of candidate divisors is $[c-2R,c+2R]$. The proof uses only the input bound and a finite count of possible equations. Whether lattice reduction finds a short equation at a larger radius depends on the input and the center. [Uniform window theorem](../PrimeFactors/SiftedDivisorWindow.lean)

## Matched searches

Each pair used the same input, public lower-quartile center, radius, Taylor depth three and seven rows. The comparison used the previous centered binomial basis. A missed height bound leaves the entire input unresolved.

| Input | Radius in odd positions | Sifted basis | Previous basis |
|---|---:|---|---|
| 132,079 | 16 | Found 269 in $[253,317]$ | Height test missed |
| Fresh 2,048-bit control | $2^{440}$ | Excluded, no root modulo 13 | Height test missed |
| Crossed 2,048-bit control | $2^{440}$ | Height test missed | Height test missed |
| Both controls | $2^{441}$ | Both missed | Both missed |
| Crossed control, follow-up | $3\cdot2^{438}$ | Excluded, no root modulo 11 | Height test missed |

The earlier checked exclusions on both large inputs used radius $2^{439}$. The fresh exclusion doubles that radius and the crossed exclusion increases it by half. The crossed intermediate radius was selected after the shared larger radii missed. Both inputs remain unresolved. The fixture records the actual lattice work in every comparison, including misses. [Fresh exclusion](https://marius-bughiu.github.io/prime-factors/#sifted-divisor-window-fresh-440) · [Crossed exclusion](https://marius-bughiu.github.io/prime-factors/#sifted-divisor-window-crossed-three-quarters) · [Reproducible inputs and budgets](../benchmarks/sifted-divisor-window.json)

Three companion results address the cost of finding the right interval. Resizing the old windows can save less than a factor of four in the number of coefficient slots for a complete sweep of either example. A two-batch rule would select one window if a particular analytic function could be evaluated efficiently at the required heights. For adjacent interval products, inexpensive updates depend only on the edges once a common product is known. Computing that first product remains a cost. [Cost of a full sweep](counting-binomial-coefficients.md) · [Two batches of readings](two-batches-of-boundary-readings.md) · [Neighboring interval products](reusing-neighboring-interval-products.md)
