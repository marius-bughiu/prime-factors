# When a weighted trace wraps

On the product **1,784,821**, an extra lookup returned **1,249 × 1,429**. Fourteen candidate sums and six table entries sufficed. None of those sums shared a divisor with the product. The ordinary row checks, the checks at the assigned gap, and the integer-square comparison across all 84 combinations yielded no factor. Ordinary Fermat factorization found the same pair in four square tests. It tests midpoints 1,336 through 1,339, where the difference of squares is $90^2$. We found this example by scanning small prime pairs for that particular behavior. [Lean certificate](../PrimeFactors/WrappedGapExample.lean) · [Comparison methods](comparing-weighted-powers-at-both-primes.md)

We then tested **all 12,994 products of distinct primes of the same width from 9 through 11 bits**, with the same base and limits. Comparing different gaps found factors on 347 products missed by the same-gap comparison with its preliminary checks. After also testing candidate gcds and integer squares, only 1,784,821 remained. Ordinary Fermat found this pair in four guesses. It was the sole extra case across both possible product lengths at each width. The full-size tests have a separate all-base calculation. [Census and its six strata](../research/wrapped-gap-census.json) · [Census and Lean certificate generator](../experiments/wrapped_gap_census.py) · [Every starting number at full size](trying-every-base-in-a-fixed-power-comparison.md)

## What the extra lookup measures

Let $N=pq$ for distinct odd primes, let $u$ be a unit modulo $N$, and let $O$ be its multiplicative order modulo $N$. For a public weight sum $c$, a candidate weighted sum $s$, and a table gap $e$, set $h=(N-1)/2$, $X=u^{s-(h+1)c}$ and $Y=u^{he}$. At a right entry with $\gcd(Y^2-1,N)=1$, the traces match and $\gcd(X-Y,N)$ is proper **if and only if** one of these two congruences holds,

$$
s\equiv Mc+Je\quad\text{or}\quad s\equiv Mc-Je\pmod O,
\qquad M=(p+q)/2,\quad J=(q-p)/2.
$$

Indeed $h-J=(p-1)(q+1)/2$ and $h+J=(q-1)(p+1)/2$. Raising $u$ to $J$ therefore agrees with $u^h$ at $p$ and with $u^{-h}$ at $q$. The difference $h+1-M=(p-1)(q-1)/2$ kills both local units as an exponent. A proper readout at a clear entry selects opposite orientations at the two primes. The trace lookup itself requires only $N,u,c,s,e$. The midpoint, gap and order in this description need not be known during a search. A proper gcd in setup is already a factor. If the precheck returns $N$, any matching trace at that entry has a difference gcd of $N$. [Exact equivalence and prechecks](../PrimeFactors/WeightedOffGap.lean)

For the original integer sum $s=ap+bq$ of the assigned weights, a clear successful match elsewhere implies the own-gap lookup would also yield a proper divisor at this same coordinate. The reason is that both entries have the same trace, and the trace determines whether the precheck is clear. Thus a new split after setup and own-gap misses arises on a proposed sum different from that true weighted sum.

## Two kinds of extra matches

If $s=Mc\pm Je$ as integers, $s^2-(c^2-e^2)N$ is an ordinary square. When $c=e$, the alternate weights are 0 and $c$. For the earlier diagnostic 91,787, the public candidate 1,052 equals four times 263. Taking its gcd with the product already finds that prime. A lookup with the wrong assigned gap is therefore insufficient evidence for genuinely different arithmetic. [Original diagnostic and its cheaper check](comparing-weighted-powers-at-both-primes.md)

At $N=1784821$, the hit is in row 45 with public weights 5 and 9, candidate $s=17924$, and a different gap $e=3$. The alternate sums are 19,016 and 18,476. **19,016 exceeds the candidate by exactly 1,092**, the order of base 2 modulo this product. The ordinary discriminant is negative, $-12,491,751$. The modular powers are 1,779,742 and 1,422,528. Their common trace is 319,977, and the gcd of their difference with $N$ is 1,249. Lean checks these powers, the trace, the proper gcd, both primes and the exact order. The independent finite comparison uses base 2, multiplier at most 64 and the first two coordinates in each eligible interval. [Arithmetic certificate](../PrimeFactors/WrappedGapExample.lean) · [Candidate generation](../experiments/weighted_global_trace.py)

## What this says at 2048 bits

In the project's full-width rectangle for two 1,024-bit primes, a wrapped match requires $O<2^{1370}$. Every left sum is at most $2^{1367}$, its weight sum is at most $2^{345}$, and any right gap from the table is at most $2^{344}$. Both $M$ and $|J|$ are below $2^{1024}$. Each of $|s-Mc\pm Je|$ is therefore smaller than $2^{1370}$. When $O$ reaches that threshold, divisibility by $O$ forces the difference to be zero, and the alternate discriminant must be an integer square. A lookup can still compare against many gaps at once. The order threshold alone supplies no frequency estimate for a fixed base or speedup on random 2,048-bit inputs. [Width bounds and full-size implication](../PrimeFactors/WeightedOffGap.lean)

There is also a bound on duplicate useful gaps. Write $L$ for the joint period of $u^h$ modulo the two primes. Once gap $e$ has opposite local orientations, precisely the gaps congruent to $e$ or $-e$ modulo $L$ have them. If twice the largest gap is less than $L$, a fixed candidate has at most one such positive gap. Separately, for fixed $c$ and a list of $k$ right gaps, at most $2k$ of the $O$ possible exponent residues can yield a split at a clear entry. A probability interpretation of $2k/O$ assumes a uniform exponent. The search chooses its exponents from specific square windows. [Gap classes and residue budget](../PrimeFactors/WeightedOffGap.lean)


## Which duplicate entries matter?

If the search checks every gap through a bound and none splits the number, either both reduced orders are one or both exceed the bound. The same conclusion follows from one final gcd after powering through the relevant prime powers. For a sparse list, a repeated trace key either gives a factor during setup or allows us to keep one representative. On the 12,994-product census, doing every duplicate check up front cost 60 extra gcds. Delaying the checks until a key is used saved two. Checking for exact equality and inversion using the powers already stored saved 4,279 gcds on its own. Both 2,048-bit controls had zero duplicate keys within the tested limits. [Lean proof](../PrimeFactors/DenseGapPrecheck.lean) · [Measured costs](batching-local-weight-gap-powers.md)
