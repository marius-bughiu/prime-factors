# Which convergents can reach a target square?

For a uniformly chosen product of two distinct 1,024-bit primes with a 2,048-bit product, **fewer than one in 65,536** can have a positive continued-fraction norm of the form $2t^2$ or $3t^2$ at *any* rational denominator $y\le2^{464}$, across **all** multipliers $1\le k\le320$. A search can therefore skip those square tests with a quantified population loss. It still has to walk the continued fraction. A separate attempt to choose better multipliers from their first positive norms recovered seven of 64 fresh small products. The ascending order recovered eight. [Lean population bound](../PrimeFactors/SmallConvergentTargetPopulation.lean) · [Reproducible experiment](../experiments/target_positive_norm_order.py)

## Why the denominator matters

Write a positive convergent to $\sqrt{kN}$ as $x/y$, in the sense that its signed norm $Q=x^2-kNy^2$ is positive. The complete denominator $Q$ satisfies $Q<2\sqrt{kN}$. In the continued-fraction recurrence, let $Q'$ be the preceding complete denominator and $P$ the new offset. Then $Q'Q=kN-P^2$. The quotient was rounded down, giving $0<\sqrt{kN}-P<Q'$. Multiplying by $\sqrt{kN}+P$ proves the bound. The rational denominator $y$ and the complete denominator $Q$ are different integers. [Recurrence used by the search](../experiments/pell_pairs.py)

Fix $D\in\{2,3\}$ and suppose $Q=Dt^2$. When $y\le 2^b$, $b\le500$, $k\le320$ and $N<2^{2048}$, the equations give $x<2^{1029+b}$, $t<3\cdot2^{513}$ and $0<ky^2<2^{1023}$. Now fix just the triple $(D,x,t)$. The integer

$$x^2-Dt^2=N\,(ky^2)$$

contains both 1,024-bit prime factors of $N$. Its remaining cofactor is smaller than either prime. Consequently the same triple cannot belong to a second eligible product, even with a different $k$ and $y$. Counting the triples gives fewer than $2^{1545+b}$ products admitting *any* such witness. The explicit prime-count inequalities of Dusart give a population of at least $2^{2025}$ distinct eligible products. The resulting fraction is less than $2^{b-480}$. For $b=64,256,384,464$, this gives respectively $2^{-416},2^{-224},2^{-96},2^{-16}$. The count covers both targets together. Later convergents can have arbitrarily larger denominators as inputs grow. A fixed row budget does not imply any of these denominator cutoffs. [Finite count and denominator inequalities](../PrimeFactors/SmallConvergentTargetPopulation.lean) · [Population and analytical premises](how-many-full-size-prime-pairs.md)

## What the cutoff saves at 2,048 bits

On the two earlier full-size inputs, each search took exactly 2,048 transitions and visited 1,024 positive norms. Modulus 3 had negative Jacobi symbol on the fresh product, so only target 2 was eligible there. The table gives ascending-multiplier results. The lossless square sieve tests ordinary square residues modulo 64, 63 and 65. The combined method tracks $y$ until it exceeds $2^{464}$. It advances through every early row and applies the square sieve only after that point. No method found a target root on either input.

| Input and target | Direct integer square roots | With square sieve | With sieve and cutoff | Sieve CPU | Sieve and cutoff CPU |
|---|---:|---:|---:|---:|---:|
| Fresh, $D=2$ | 345 | 21 | 1 | 6.91 ms | 6.76 ms |
| Crossed, $D=2$ | 349 | 12 | 0 | 6.95 ms | 6.78 ms |
| Crossed, $D=3$ | 519 | 10 | 0 | 6.99 ms | 6.86 ms |

These are medians of eight rotated measurements on ARM64 macOS using Python 3.9.6, including multiplier selection and denominator tracking. Reconstructing the ordinary convergents independently verified the numerators, denominator heights and exact omitted tests. Most of the runtime remained in work shared by the methods. The population bound applies to uniformly chosen products before seeing their values. It does not estimate the success probability for either of these two fixed inputs. [Control inputs](../benchmarks/projected-divisor-wheel.json) · [Comparison and independent replay](../experiments/target_positive_norm_order.py)

## Did choosing a multiplier by its first norm help?

Let $s=\lfloor\sqrt{kN}\rfloor$, $h=kN-s^2$ and $a=\lfloor2s/h\rfloor$. The first upper convergent is $(as+1)/a$ and its positive norm is exactly $Q_2=1+a(2s\bmod h)$. The spacing between consecutive values $Dt^2$ grows with $t$, so small positive norms have a denser set of possible targets nearby. The experiment tests whether a small $Q_2$ also predicts useful *later* norms. The spacing calculation alone gives no such implication.

We froze the rule before generating 32 products each of 20- and 24-bit primes with the new SHAKE256 domain `target-positive-norm-order-v1/<bits>`. We ran both targets whenever their public Jacobi symbol was positive. There were 66 eligible product-target combinations. All three methods used the same local multiplier gate, up to 256 rows per walk and exactly 2,048 actual transitions per combination. The two pilot methods examined the first two rows of every eligible walk and counted any target immediately. They spent their remaining transitions in ascending multiplier order or in increasing $Q_2$ order, breaking ties by multiplier. All methods continued to the fixed cap to give an equal-work comparison. [Local gate](../PrimeFactors/TargetNormMultiplier.lean) · [Product generator](../experiments/affine_radix_holdout.py)

| Method | Product-target cases with a root | Cases split | Distinct products split | 20-bit $D=2$ case batch CPU | 24-bit $D=2$ case batch CPU |
|---|---:|---:|---:|---:|---:|
| Ascending multiplier | 17 | 8 | 8 | 30.44 ms | 29.04 ms |
| Two-row pilot, then ascending | 20 | 10 | 9 | 31.47 ms | 29.78 ms |
| Two-row pilot, then smallest $Q_2$ | 21 | 8 | 7 | 31.38 ms | 29.66 ms |

The smallest-$Q_2$ rule gained six root cases and lost two relative to plain ascending. It gained two split cases and lost two, with some products reached under both targets. All successful splits were at the smaller width. Each method visited 135,168 rows. The pilots started 2,035 walks each, compared with 528 for ascending. Lean checked the prime factors of all nine distinct products recovered by at least one method. For example, the geometry order gained $509327565977=561607\cdot906911$ and missed $408342064079=549431\cdot743209$, which ascending found.

To reproduce the small panel, run `python3 -m experiments.target_positive_norm_order --output build/target-positive-norm.json`. Recheck its prime certificates with `python3 -m experiments.target_positive_norm_order --verify-report build/target-positive-norm.json`. Use `python3 -m experiments.target_positive_norm_order --full-size` for the full-size denominator census and timings. [Experiment and counters](../experiments/target_positive_norm_order.py)
