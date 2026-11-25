# Combining two signed factor lanes by multiplying the input by three

For some degrees, one polynomial for $3N$ covers two residue groups that each require a polynomial for $N$. On the existing product 43,657, the degree-four search used nine lattice reductions in place of seventeen. At degree six on the same input, both searches needed nine. The Taylor method saves calls when accommodating the larger factors leaves the dyadic radix unchanged. With the sharper Newton method, removing powers of three from the usable factorials costs at least one extra radix bit throughout the nontrivial range. The baseline already uses factor exchange and simultaneous negation. [Lean coverage and scale checks](../PrimeFactors/MultiplierLaneCover.lean) · [Signed lane implementation](../experiments/quartic_factor_lanes.py)

## Coverage and its cost

Take an odd balanced product $N=pq$, with $p,q$ in a known interval $[B,X]$, and a radix $R$ coprime to $TN$. Each divisor $a$ of a public multiplier $T$ gives the pair $(ap,(T/a)q)$ for the product $TN$. Testing a transformed first coordinate $v$ modulo $R$ can cover original residues $a^{-1}v$. If $A$ is the set of usable multipliers and $V$ the tested residues, the union has at most $|A||V|$ elements. Multipliers equal modulo $R$ and intersections between different translates reduce coverage. With both $a$ and $T/a$ bounded by $K$, the elementary coordinate bound becomes $KX$. [Finite cover theorem](../PrimeFactors/MultiplierLaneCover.lean)

For degree $2m$, the sufficient LLL radix grows in proportion to $K^{(m+1)/(2m+1)}$ before rounding. Every multiplier has $K\ge\sqrt T$, while its number of divisors grows more slowly than every positive power of $T$. To see the latter, fix $\epsilon>0$. For a prime $p$ large enough, $h+1\le2^h\le p^{\epsilon h}$ for all $h\ge0$. For each of the finitely many smaller primes the ratio $(h+1)/p^{\epsilon h}$ is bounded. Multiplying over prime powers gives $\tau(T)\le C_\epsilon T^\epsilon$. Consequently, allowing the multiplier to grow does not improve the exponent through this coordinate bound and divisor count alone. Small multipliers can still change a finite budget. [Proved scale exponents](../PrimeFactors/PowerFactorScale.lean)

## Selecting the lanes for three

Assume $3\nmid N$ and use $R=2^e$, $e\ge 4$. The candidates for any original pair are $(p,3q)$ and $(3p,q)$, together with exchange and negation. After root recovery, discard values that do not divide $3N$. Exactly one coordinate of any divisor pair of $3N$ is divisible by three. Divide that coordinate by three and verify that the two resulting integers multiply to $N$ and satisfy the original balance condition. A multiple of three as the original input exposes the divisor three directly.

The odd residue classes modulo sign are exactly the powers of three with exponents modulo $L=2^{e-2}$. The identity that $3^{2^{h+1}}-1$ is divisible by $2^{h+3}$ and has odd quotient proves this by lifting one bit at a time, starting from $1,3,-1,-3$ modulo eight. The number of representatives matches the number of classes, so the list has no repeats. The same lift finds the exponent $k$ with $N\equiv\pm3^k\pmod R$ in $O(e)$ modular-power tests using successive squaring or incrementally lifted residues. [Signed-power and lifting proofs](../PrimeFactors/MultiplierLaneCover.lean)

Exchange sends exponent $i$ to $k-i$ modulo $L$. Put $s=\lceil k/2\rceil$. Starting at $s$, one representative of each original signed, unordered class is $s+j$ with $0\le j<V$, where

$$
 V=L/2+1-(k\bmod 2).
$$

The interval and its reflection cover the cycle. For even $k$ its two endpoints are fixed and all other positions occur in pairs. For odd $k$ there are no fixed points. A polynomial for the transformed residue $3^{s+j}$ covers original positions $j$ and $j-1$. For each $t=0,\ldots,\lceil V/2\rceil-1$, select position $\min(2t+1,V-1)$. Every position is covered, using exactly $\lceil V/2\rceil$ transformed lanes. For nonempty coordinate ranges the root search can inspect the four signed intervals $[B,X]$, $[-X,-B]$, $[3B,3X]$ and $[-3X,-3B]$. [Folded path and endpoint coverage](../PrimeFactors/MultiplierLaneCover.lean)

## When the radix stays the same

Write $d=2m+1$ and $h=m(m+1)$. For the multiplier-three route at $R=2^e$, the sufficient condition on $X$ is

$$
 d^d 2^{md} 3^{2h} X^{2h}<2^{2mde}.
$$

Use $X^2<2^{2049}$ for any 2,048-bit balanced product. Direct integer comparison gives the *same* sufficient $e$ for both strategies at degrees eight and sixteen. The next lower dyadic radix fails the unmultiplied test on the worst-case envelope for each row. The number of original signed classes is $2^{e-3}$ or $2^{e-3}+1$ depending on $N$ modulo eight. At the same radix the number of transformed tests is $2^{e-4}$ or $2^{e-4}+1$, respectively. [Exact scale inequalities](../PrimeFactors/MultiplierLaneCover.lean)

| Degree | Rank | Sufficient $e$ for $N$ | Sufficient $e$ for $3N$ | Unmultiplied / multiplied lane counts, up to one |
| ---: | ---: | ---: | ---: | ---: |
| 8 | 9 | 571 | 571 | $2^{568}$ / $2^{567}$ |
| 16 | 17 | 544 | 544 | $2^{541}$ / $2^{540}$ |

At the same radix both methods reduce the same lattice dimension. The centered triangular basis entries still use the same moduli. Scaling column $j$ by $(3X)^{|j-m|}$ instead of $X^{|j-m|}$ adds at most $\lceil m\log_2 3\rceil$ bits to the worst-case bit bound for a scaled entry. Substituting $3N$ likewise adds at most this many bits to each power of the input used in constructing a relation. The four root intervals can require more subdivision work per polynomial. Halving the lattice calls therefore gives a count for the expensive operation, while total bit operations and runtime at full width remain unmeasured.

If the radix must double, the extra coverage cancels the entire gain in lane count. That happens at the previously reported degree 4,096, where the exact worst-case sufficient exponents for these bounds are 513 and 514. Both approaches then need about $2^{510}$ signed classes. The larger input and additional root intervals can still increase cost per polynomial.

## What changes with the Newton basis

The Newton construction divides the squared radix threshold by the square of the product of the usable factorials through $2m$. For the input $N$ coprime to three, these factorials retain all their powers of three. For the transformed input $3N$ the current algorithm removes them. Put $S=\sum_{j=0}^{2m}v_3(j!)$. Combining this loss with $X\mapsto3X$ increases the **unrounded** required radix by exactly

$$
3^{[m(m+1)+S]/[m(2m+1)]}.
$$

For $m\ge2$, $S\ge\sum_{j=1}^{2m}\lfloor j/3\rfloor\ge(2m^2-3m)/3\ge m(m-1)/3$. The last bound also holds for $m=1$. The ratio is therefore at least $3^{2/3}>2$. For dyadic radices chosen by the strict determinant test, this forces at least one extra bit. Doubling the radix leaves the same lane count after grouping, and quadrupling it increases the count. An imposed minimum radix can mask rounding on tiny examples. This argument applies to the current choice of factorials coprime to the transformed product. [Newton divisibility and thresholds](../experiments/newton_lanes.py) · [Difference-lane derivation](difference-lanes.md)

The table uses the same worst-case envelope $X^2\le2^{2049}$ and assumes the input factors exceed $2m$, as they do for balanced 2,048-bit semiprimes at these degrees. Each entry is the dyadic exponent for $N$ followed by the one for $3N$. The driver sums the exact prime valuations in the threshold, and bounds the resulting logarithm between rational numbers using integer powers. It doubles the precision until both bounds certify the same exponent. [Reproducible scale calculation](../experiments/multiplier_lane_cover.py)

| Degree | Taylor exponents | Newton exponents | Newton lane count after grouping |
| ---: | ---: | ---: | --- |
| 4 | 616 / 617 | 615 / 617 | Approximately doubles |
| 6 | 587 / 588 | 586 / 587 | Equal |
| 8 | 571 / 571 | 569 / 570 | Equal |
| 16 | 544 / 544 | 541 / 543 | Approximately doubles |
| 64 | 521 / 522 | 517 / 519 | Approximately doubles |
| 1,024 | 514 / 515 | 506 / 507 | Equal |
| 2,048 | 514 / 514 | 505 / 506 | Equal |
| 4,096 | 513 / 514 | 504 / 505 | Equal |

## Small complete comparisons

The comparison used the least dyadic radix satisfying the displayed strict inequality separately for each method, with $X=\lfloor\sqrt{2N}\rfloor$ and the factor $3^{2h}$ omitted for the baseline. The baseline used the repository's signed CRT representatives. The multiplier used the consecutive-exponent schedule above. For each chosen residue with a nonempty coordinate interval, the same `equation` and `integer_roots` routines constructed the lattice polynomial and tested the respective intervals. Every recovered pair passed product and balance checks. The complete searches agreed on all factor pairs. [Lattice implementation](../experiments/quartic_factor_lanes.py) · [Integer root isolation](../experiments/norm_auxiliary.py)

| Input | Degree | Radix $N$ / $3N$ | LLL calls | LLL swaps | Root-search nodes | Median milliseconds |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1,225 | 8 | 32 / 32 | 5 / 3 | 1,127 / 454 | 9 / 10 | 12.85 / 5.92 |
| 34,387 | 4 | 64 / 128 | 8 / 8 | 307 / 341 | 18 / 38 | 2.04 / 2.49 |
| 43,657 | 4 | 128 / 128 | 17 / 9 | 778 / 385 | 36 / 38 | 4.84 / 2.65 |
| 43,657 | 6 | 64 / 128 | 9 / 9 | 917 / 1,053 | 22 / 48 | 8.27 / 10.34 |

Timings are medians of five alternating local Python runs. They include the bit-by-bit lookup for $k$, generation of representatives and all lane computations. The counts determine the comparison independently of these timings. On 43,657 both methods found 149 and 293. The large-input rows above give search budgets only.


On 43,657 at degree four, the Newton baseline used radix 64 and nine lattice reductions, taking a median 2.67 ms. The multiplier needed radix 128 and still used nine reductions, taking 3.05 ms. The baseline Newton run and the multiplied Taylor run were similar in elapsed time on this input. On 1,225 at degree eight, Newton changed from radix 8 to 32 and from two lattice reductions to three. [Reproduction driver](../experiments/multiplier_lane_cover.py) · [Regression tests](../tests/test_multiplier_lane_cover.py)

These commands reproduce the comparisons and full-size scale table from the repository root.

```sh
python3 -m experiments.multiplier_lane_cover fixtures --basis taylor
python3 -m experiments.multiplier_lane_cover fixtures --basis newton
python3 -m experiments.multiplier_lane_cover scales
```
