# Which cyclotomic measurements distinguish the prime sum?

For $551=19\cdot29$, consider the sums 47, 48 and 49. All three fit the size bounds if we allow real factors with product 551. A single value of a polynomial defined by 551 distinguishes them. The largest obstacle is obtaining that value. In our small product-only replay, building the polynomial took 596 trial divisions and already encountered both primes. Ordinary Fermat search split 551 at its first midpoint, 24. [Independent measurement and operation counts](../benchmarks/inverse-cyclotomic-measurements.json) · [Replay code](../experiments/inverse_cyclotomic_measurements.py)

## One real reading

Write $N=pq$, where $B\le p<q<2B$ are primes. Define the inverse cyclotomic polynomial $\Psi_N=(X^N-1)/\Phi_N$ and set $T_N=(X-1)\Psi_N$. Moree’s binary inverse cyclotomic identity gives $T_N(X)=(1-X^p)(1-X^q)$. Its left side is specified by the public integer $N$. Evaluating the right side directly uses the unknown factors. [Moree’s 2009 paper](https://www.sciencedirect.com/science/article/pii/S0022314X0800200X) · [Polynomial identity in Lean](../PrimeFactors/InverseCyclotomicMeasurements.lean)

Take $x=\exp(-1/(8B))$. For every candidate integer sum $s$, the two trial factors are $(s\pm\sqrt{s^2-4N})/2$. Keep real pairs in the known size interval. As the sum grows, $(1-x^a)(1-x^b)$ decreases. A change of one in the sum changes the reading by at least $1/(2592B)$, including when the factors are close together. If the input is within $1/(8192B)$ of the true reading, only the true sum has its exact trial value within that tolerance of the input. At $B=2^{1023}$, rounding the input to the nearest multiple of $2^{-1035}$ gives that accuracy. [Separation along the curve of constant product](../PrimeFactors/CyclotomicProductCurve.lean)

For $B=16$ the three intervals below are disjoint. Lean bounds the exponentials by rational polynomials and the candidate roots by rational intervals.

| Trial sum for 551 | Certified range of the reading |
| ---: | --- |
| 47 | $0.028068<T<0.028069$ |
| **48** | **$0.027965<T<0.027966$** |
| 49 | $0.027863<T<0.027864$ |

Both neighboring readings differ from the middle one by more than $0.000101$. At sum 48 the discriminant is $48^2-4\cdot551=100$, giving the prime pair 19 and 29. For this small control, parity also selects 48 because both prime factors are odd. Acquiring the value independently from the polynomial coefficients gave the interval $[0.027965883523,0.027965883526]$ using 48 interval multiplications after constructing the polynomial. [All feasible integer sums and certified intervals](../PrimeFactors/SingleCyclotomicValueControl.lean) · [Independent interval measurement](../benchmarks/inverse-cyclotomic-measurements.json)

For $32{,}881=131\cdot251$, sums 370 and 382 both survive the public congruence for the prime sum modulo four and the square-discriminant tests modulo 16, 3, 5 and 7. The single reading at $x=\exp(-1/1024)$ lies between 0.026104 and 0.026105. Sum 370 predicts a value between 0.026248 and 0.026249, so the measurement selects **382**. The polynomial constructor used 33,260 trial divisions. Checking the discriminant modulo 11 already eliminates 370, and direct Fermat search succeeds on its tenth midpoint. [Certified candidate ranges and modular checks](../PrimeFactors/SingleCyclotomicValueControl.lean) · [Operation counts](../benchmarks/inverse-cyclotomic-measurements.json)

The separation bound comes from the function $f(z)=z/(e^z-1)$. Lean bounds its derivative above by $-9/32$ for $0<z\le1/4$. Applying this estimate while moving the larger trial factor along the curve $ab=N$ avoids division by the difference of nearly equal factors. This argument uses elementary real analysis. [Slope proof](../PrimeFactors/CyclotomicValueSlope.lean) · [Classical generating function](https://dlmf.nist.gov/24.2#E1)

## Two rational readings with a counted decoding cost

Choose the rational $r=1-1/(8B)$. For odd primes, averaging $T_N(r)$ and $T_N(-r)$ cancels the individual terms $r^p$ and $r^q$, giving

$$\frac{T_N(r)+T_N(-r)}{2}-1=r^{p+q}.$$

The two readings lie in $[0,1]$ and $[1,4]$. At the 1,024-bit factor width, **1,029 fractional bits in each rounded-to-nearest reading suffice**. Given those values, at most 1,026 comparisons identify the sum. Each comparison uses at most 2,052 fixed-point multiplications whose operands are at most 2,059 bits. This counts decoding after the two values are supplied. Whether the readings can be obtained cheaply from a full-width product remains open. [Accuracy and comparison count](../PrimeFactors/InverseCyclotomicMeasurements.lean) · [Power separation](../PrimeFactors/BoundedPowerMeasurement.lean) · [Rounded multiplication costs](../PrimeFactors/RoundedUnitPowers.lean)

For 551 the two measurements at $r=127/128$ round to $115/4096$ and $13699/4096$. Their average minus one is $2811/4096$. Six comparisons return 48. The independent replay constructs $\Phi_{551}$ and $\Psi_{551}$ from the index, checks the two rounded readings, and has Lean verify the resulting factorization. [Numerical receipt](../benchmarks/inverse-cyclotomic-measurements.json)

## Can a short Taylor prefix supply the readings?

At the positive rational point $r$, every ordinary Taylor truncation of $T_N$ ending before degree $p+q$ has absolute error at least $1/18$. At degree $p+q$ the result is exact. A direct scan from degree zero must therefore visit at least $2^{1024}+2$ coefficient positions for distinct 1,024-bit primes, even to get below this constant error. For 551 the exact cutoff is degree 48. The proof covers dense scans. Exploiting the four nonzero terms requires locating their exponents or a different way to aggregate them. [Exact cutoff and slot count](../PrimeFactors/InverseCyclotomicTruncation.lean)

The two-point projection makes this obstruction visible. Every prefix before degree $p+q$ contains only its constant and a subset of the two odd prime powers. Its projection is exactly zero at any pair of opposite points, whereas the full projection at $r$ is at least one half. The pinned RH statements concern zeros of zeta and Dirichlet $L$-functions. An estimate that supplies this individual polynomial reading from $N$ would require a further argument. [Projection proof](../PrimeFactors/InverseCyclotomicTruncation.lean) · [Pinned analytic statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)

## Which coefficients carry information?

The coefficient of $\Psi_N$ at index $k$ is negative exactly when $k<p$. With access to those signs, a binary search for a 1,024-bit smaller prime needs at most 1,023 queries. That is a bound on the number of supplied signs. [Coefficient formula and bisection](../PrimeFactors/InverseCyclotomicThreshold.lean)

The ordinary polynomial $\Phi_N$ gives a different answer at the same index. Below degree $2p$ it matches $(1-X)(1+X^p+X^q)$, with an exact correction of $+1$ at degree $2p$. In the odd positions from $B$ through $2B-1$, its nonzero coefficients identify exactly $p$ and $q$. A direct scan over all such odd positions at the target width examines $2^{1022}$ indices. Summing their positions gives $p+q$. Over all positions from 0 through $2B$ and for $B<p$, the signed second moment is $-2(p+q)-3$. [Sharp coefficient cutoff](../PrimeFactors/BalancedCyclotomicPrefix.lean) · [Moment and scan costs](../PrimeFactors/CyclotomicPrefixMeasurements.lean) · [Moree on the classical semigroup identity](https://arxiv.org/abs/1308.3972)

Even if a 64-bit function of the product selects a probing strategy, $2^{64}$ adaptive low coefficient or prefix-sum queries within the word band return a nonzero reply on fewer than one in $2^{879}$ eligible prime pairs. Another bound covers probes anchored at the product’s square root. With up to $2^{128}$ fixed signed offsets, fewer than one in $2^{877}$ eligible pairs meets a prime-dependent position. These statements specify how the indices may depend on the product. [Unconditional coverage bounds and query model](../PrimeFactors/CyclotomicCoefficientProbePopulation.lean)
