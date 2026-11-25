# How much work does checking every group require?

We ruled out one group of guesses on the fresh 2,048-bit product in 0.76 seconds. Could we just make each group bigger until the whole search fits on a PC? Lean proves a limit for the current search. Even if it chooses the group size anew every time, covering every possible odd 600-bit remainder takes at least $2^{247}$ units of work on that product. Finding one successful guess early remains possible. The open problem is how to choose that guess from the product. [Measured exclusion](projected-quartic-levels.md) · [Proof for the fresh product](../PrimeFactors/ProjectedSweepBudget.lean)

## What counts as work?

A query guesses the last $e$ binary digits of a factor, using modulus $R=2^e$. We allow every $e$ from 0 to 600, and credit the query with two remainders to allow either prime to come first. A query computes one lattice reduction and tests a whole interval in blocks of up to 65,536 positions. For the conservative count we charge the larger of one and the number of blocks. Counting the reduction and the blocks separately gives a stronger bound of $2^{248}$ on the fresh input. Timings per block can differ. Neither count gives a time to the first successful guess. [Search implementation](../experiments/projected_level_sieve.py)

## Why changing the group size has a cost

* A query covers at most $2\cdot2^{600-e}$ possible 600-bit remainders. This upper bound allows the two groups to overlap and credits a query even for remainders with no actual factor.
* The scanner uses four positive weights from the public product. Its spread $S$ is the sum of the four weights times the absolute values of integer coefficients, with at least one nonzero coefficient. Thus $S$ is at least the smallest weight $w$. A complete scan of the interval $[C-S,C+S]$ tests at least $\lfloor2S/(360R^4)\rfloor$ positions for every possible integer offset $C$.
* On the fresh input $2w\ge360\cdot2^{1009}$. For $e\le248$ the scan therefore needs at least $2^{249-e}$ blocks. For $e\ge249$, even a single unit suffices to give $R\cdot\mathrm{work}\ge2^{249}$. Combining this inequality with the first item gives at most $2^{352}$ fine remainders per unit, for any mix of group sizes.

There are $2^{599}$ odd 600-bit remainders. To cover them all costs at least $2^{599}/2^{352}=2^{247}$ units. Overlapping queries only reduce the total coverage. The proof applies to any sequence of completed queries, including choices made after seeing earlier results. It assigns no probability to the true remainder and assumes the present scanner visits its level blocks. A shortcut that identifies promising groups from the product, or rejects an interval without visiting its blocks, changes the problem. [Coverage and cost theorems](../PrimeFactors/ProjectedSweepBudget.lean)

## Which other products satisfy the bound?

Let $X=2^{1023}$, so both putative factors are in $[X,2X-1]$. Lean proves the same $2^{247}$ bound throughout $2X^2\le N\le3X^2$, the lower half by numerical value of the 2,048-bit interval. In that range the public upper bound on either factor is $U=2X-1$. The gap between $U+\lfloor N/U\rfloor$ and $\lceil2\sqrt N\rceil$ is still wide enough to force work even when the query uses its smallest possible nonzero coefficient. Writing $b=X/256$, Lean checks that all four weights are at least $3b$, which gives the required inequality. The fresh input lies above this band and has its own direct proof. [Interval proof and complete-sweep theorem](../PrimeFactors/ProjectedSweepRange.lean) · [Weights used by the search](../experiments/centered_sum_quartic.py)
