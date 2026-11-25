# How many records does the full Farey search require?

For a 2,048-bit input, the complete compressed Farey schedule in this repository has **more than `2^404` records**, for every choice of denominator limit `K ≥ 1` and baby-table length `m ≥ 1`. A record here is one primitive slope to set up, one baby-table entry, or one giant block to process. A factor found at setup or in the first few blocks can end a run early. The bound applies to the full schedule, independently of which slopes produce collisions. It gives neither a lower bound on time to the first factor nor a lower bound for other factoring algorithms. [Window implementation](../experiments/weighted_windows.py) · [Stride and block implementation](../experiments/weighted_stride_search.py)

## A lower bound for one window

Fix a reduced slope `a/b` with `1 ≤ b ≤ K` and `b ≤ a ≤ 2b`. Write `A = 4abN`. The interval of possible weighted sums starts at `L = ceil(√A)`. On either available side of the slope, let `h` be the sum of its denominator and that of the adjacent Farey slope. The upper endpoint `U` is at least the integer square root of

```text
A + floor(bN / [h(ha ± 1)]).
```

Every slope, including either endpoint, has an available side. Since `h ≤ 2K` and `a ≤ 2b`, its positive denominator is at most `h(ha+1) ≤ 10bK²`. Thus a radicand gain of at least `floor(N/(10K²))` is available at each slope.

Put `s = floor(√N)`, `y = floor(√A)`, and `j = floor(s/(64K³))`. For `s ≥ 16`, the inequality `N < (s+1)²` implies `8N ≤ 9s²`. It follows that `y ≤ 3Ks`. From `64K³j ≤ s` we get `20y+10j ≤ 64Ks`. Therefore

```text
(2yj + j²)·10K² = jK²(20y+10j) ≤ 64K³js ≤ s² ≤ N.
```

This proves `U ≥ y+j`. Since `L ≤ y+1`, the inclusive window contains at least `j` consecutive integers. This estimate also covers `j = 0`.

The search keeps one residue class modulo a step of at most 24. If a window produces `g` giant blocks of at most `m` retained labels each, then `j ≤ 24(1+mg)`, allowing for the initial offset and final incomplete block. The definition of `j` gives

```text
s+1 ≤ 64K³(j+1) ≤ 1600K³(1+mg).
```

## Combining all the windows

Let `R` count the primitive slopes. Among the `K²` ordered pairs of integers from 1 to `K`, at most `3K²/4` have a common divisor larger than 1. Indeed, divisor `d` covers at most `(K/d)²` pairs, and

```text
Σ(d≥2) 1/d² ≤ 1/4 + Σ(d≥3) 1/[d(d−1)] = 3/4.
```

Swapping coordinates places at least half the surviving pairs in the triangle `1 ≤ x ≤ b ≤ K`. Each pair there gives a distinct primitive slope `(b+x)/b`. Hence `K² ≤ 8R`, even before counting `1/1`.

Let `G` be the total number of giant blocks and `W = R+G+m`. Summing the per-window inequality gives `(s+1)R ≤ 1600K³(R+mG)`. With `K² ≤ 8R`, this implies `s+1 ≤ 12800K(R+mG)`. Since `m ≥ 1`, we also have `4(R+mG) ≤ 4m(R+G) ≤ W²`, and `K² ≤ 8W`. Squaring and substituting yields

```text
N < (s+1)² ≤ 81,920,000 W⁵.
```

The constant is smaller than `2^27`. A 2,048-bit integer has `N ≥ 2^2047`, so `W ≤ 2^404` would contradict the inequality. The argument counts every primitive slope only once and ignores visits to unreduced fractions. [Lean proof](../PrimeFactors/FareyWork.lean)
