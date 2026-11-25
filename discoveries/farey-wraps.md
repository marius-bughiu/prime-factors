# How often can the weighted search hit a factor by modular coincidence?

A weighted search can find a factor even when its candidate label differs from the correct weighted sum. Their exponents can agree modulo the multiplicative order at one hidden prime. We bound how often this can happen in the original compressed Farey windows, allowing collisions in the padded end of each giant block.

Choose two distinct 1,024-bit primes uniformly, condition on their product having 2,048 bits, and use one uniformly random invertible base. Set the Farey order to `K = 2^204` and the baby-table size to `m = 2^408`. The probability of **any unequal-label collision at either prime, across all slopes**, is less than `2^-159`. Across a fixed selection of at most `2^200` slopes, the probability of **any local label collision**, including a correct weighted sum, is less than `2^-83`. These parameters illustrate the scale of the search. The bounds below also accept other parameter choices.

A local collision is necessary for a label comparison to expose that factor. Setup can discover a divisor independently. The random-base bounds apply to a fresh uniform unit modulo the product. For a fixed base such as 2 we give a bound conditional on its local order, and a separate estimate for coincidences that hold for every base. This analysis applies to subsets of the original Farey windows. Reallocating larger windows to surviving slopes requires substituting their new widths. [Search implementation](../experiments/weighted_stride_search.py) · [Original window endpoints](../experiments/weighted_windows.py) · [Full-schedule record bound](farey-work.md)

## The exact local period

Fix one prime factor `p`, write the other as `q`, and put `r = q/p`. Allow either prime to play the role of `p`, so `1/2 ≤ r ≤ 2`. For slope `a/b`, let `T = ap+bq`. The stride `s = gcd(24, 2(a+bN))` is even and divides 24. Both `T` and every tested label `t` are congruent to `a+bN` modulo `s`. The apparatus compares local powers with exponent difference `(24/s)(T−t)`. This follows from `a+bN ≡ T (mod p−1)` and the aligned baby table. [Formal congruence and collision](../PrimeFactors/WeightedStride.lean)

Write `H = ord_p(β^24)` for the order of the powered base. The local comparison succeeds exactly when `sH` divides `T−t`. In particular, every nonzero difference is a nonzero multiple of `2H`. To count coincidences that work for **every** unit base at this prime, take `H = (p−1)/gcd(24,p−1)`, the order attained by the 24th power of a primitive root. [Lean period identity](../PrimeFactors/FareyWrap.lean)

For example, take `N=22,999`, `K=4`, slope `4/3`, and base 2. The entire window is the single label 1,051. The factors are 109 and 211, giving a true sum of `4·109+3·211=1,069`. The difference 18 is exactly the universal local period at 109 since `s=2` and `108/gcd(24,108)=9`. The tested power is congruent to 18,204 modulo the product, and `gcd(18,203,22,999)=109`. This is a concrete factor found from a label outside the correct-sum case. [Lean certificate](../PrimeFactors/FareyWrap.lean)

## Counting the extra intervals

Define `F(r) = (√a − √(br))²`. Then `pF(r) = T−2√(abN)`. Suppose that all tested labels lie between `2√(abN)` and `2√(abN)+pε`, where `ε` may depend on the anchor prime and the slope and is uniform over partner primes. Put `D=2H/p`. An unequal-label collision requires

```text
kD ≤ F(r) ≤ kD+ε    for some nonzero integer k.
```

For `ε < D`, such a `k` must be positive. Since `1 ≤ a/b ≤ 2` and `1/2 ≤ r ≤ 2`, the squared distance is at most `b/2`. Thus there are at most `b/(2D)` positive periods. Each period has at most two intervals, one on each side of the center `a/b`.

Each of those intervals has length at most `√2 ε/√(bkD)`. Indeed, with `z=√(br)`, two points in the same interval have `z−√a` of the same sign and absolute value at least `√(kD)`. The difference of their squares implies `|Δz| ≤ ε/(2√(kD))`. The change in `r=z²/b` is at most `2√(2b)|Δz|/b`. Summing `1/√k` through `J` costs at most `2√J`. The combined length of all the extra intervals is at most `4ε/D`. [Lean branch-width and inverse-square-root lemmas](../PrimeFactors/FareyWrap.lean)

The integer partners `q` are spaced by `1/p` in the ratio. An interval of length `l` therefore contains at most `pl+1` of them. For `ε ≥ D`, the whole ratio range has at most `2p ≤ 2pε/D` integer partners. Consequently, for either range of `ε`, the number of integer partners allowing an unequal-label local collision at this slope is bounded by

```text
(5pε+b)/D.
```

For the correct label `t=T`, one needs `F(r) ≤ ε`. This is one central interval of length at most `4√(aε)/b ≤ 6√(ε/b)`. When `ε ≤ a`, subtract the squared endpoints `(√a ± √ε)²/b`. For `ε ≥ a`, the displayed bound already exceeds the length of the ratio range.

## From Farey endpoints to prime pairs

Every available neighboring denominator gives `h ≥ K+1` and `ha−1 ≥ ha/2`. The radicand gain above `4abN` is therefore at most `2bN/(ah²)`. Dividing the gain by twice the original square root bounds the increase in the upper label by `p/[b(K+1)²]`. The final partial giant block can compare up to `m−1` additional indices, at spacing at most 24. We may use

```text
ε = 1/[b(K+1)²] + 24(m−1)/p.
```

There are at most `b+1 ≤ 2b` slopes of denominator `b`. For `X ≤ p < 2X`, summing `5pε+b` over every slope gives at most `XA`, where

```text
A = 20/K + 240mK²/X + 2K³/X.
```

This envelope also covers every subset of the windows with the same `K,m`. To count universally valid coincidences, `1/D ≤ 15` for every prime `p≥5`. For a uniformly chosen unit base modulo `N`, its image modulo `p` is uniform. Its 24th power is uniform on the cyclic subgroup of order `M=(p−1)/gcd(24,p−1)`. This gives the exact expectation

```text
E[1/D] = p/(2M) · Σ(d|M) φ(d)/d ≤ 15 τ(p−1),
```

where `τ(n)` counts the divisors of `n`. The marginal base modulo a fixed `p` has the same distribution for every partner. Thus we can first sum over integer partners at a fixed local base and then average. Summing `τ(p−1)` over prime anchors is at most `Σ(n≤2X)τ(n) ≤ 2X(1+ln(2X))`, by counting multiples of each divisor. This accounts for low-order bases as well as high-order ones.

For `X=2^1023`, there are fewer than `1.511X/ln X` primes in `[X,2X)`. The band `[√2 X,2X)` supplies at least `(0.22X/ln X)²/2` unordered pairs of distinct primes; every such product has 2,048 bits. Summing over all anchors counts the event at either factor. Dividing by this lower bound for the conditional population yields the following probabilities. [Finite prime-count calculation](stride-budget.md) · [Rosser and Schoenfeld, Corollary 1](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6)

| Unequal-label collision over all original windows | Probability at most |
| --- | --- |
| One comparison succeeds at the same prime for every unit base | `30·1.511 (ln X) A / 0.22²` |
| At either prime for a uniformly drawn unit base | `60(1+ln(2X))(ln X)² A / 0.22²` |

With the indicated `K,m`, `A < 51·2^-204`, `ln X < 710`, and `1+ln(2X) < 711`. The two bounds are respectively below `2^-178` and `2^-159`.

## A preselected prefix, including the correct label

Fix any list of at most `B²` slopes before seeing the prime pair, where `B ≥ 1` is an integer. Among slopes with `b ≤ B`, there are at most `2b` at each denominator. All other terms have `b > B`. Consequently the list has `Σ 1/b ≤ 3B` and `Σ 1/√b ≤ 3B^(3/2)`. The central interval allows at most `6p/[b(K+1)] + 30√(pm/b)+1` integer partners at each slope, including the block padding. For any anchor the list therefore has at most

```text
X · (36B/K + 90√(2m/X) B^(3/2) + B²/X)
```

possible partners giving a correct label at some selected slope. Multiply the parentheses by `2·1.511 ln X/0.22²` to obtain a conditional probability bound. For `B = 2^100`, adding the random-base wrap bound above still gives a total probability below `2^-83`. For a prefix chosen using the observed product, the correct-label estimate depends on how that prefix was selected. The all-slopes wrap bound already includes every such subset.

The exact period, branch diameter, inverse-square-root sum and final rational arithmetic at the stated parameters are machine checked. The prime-population and probability estimates are paper deductions from these identities and the cited explicit prime counts. [Lean module](../PrimeFactors/FareyWrap.lean)
