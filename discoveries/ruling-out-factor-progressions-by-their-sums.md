# Ruling out factor progressions by their sums

On 15,049 the ordinary wheel leaves ten possible smaller factors. An interval test using their possible partners retains four. Checking which **sums** those same pairs could have leaves only 89, 101 and 119. The gcd of their product with 15,049 is 101, and $101\times149=15{,}049$. Lean checks the entire example. [Proof and exact candidates](../PrimeFactors/ReciprocalSumLanes.lean)

## When a progression can be skipped

Suppose $N=pq$ with $p\le q\le 2p$. For a chosen small wheel $W$ coprime to $N$, group the possible smaller factors by their remainder. In one such progression write the endpoints as $a,b=a+mW$. If its remainder is $r$, its partner must have remainder $s=N/r\pmod W$ and lie from $\lceil N/b\rceil$ to $\lfloor N/a\rfloor$. The factor sum is congruent to $a+s\pmod W$ and lies between $b+\lceil N/b\rceil$ and $a+\lfloor N/a\rfloor$.

The number of partner positions is **exactly $m$ plus the number of possible sums** in that progression. To see why, translating each endpoint of the sum interval back to its corresponding partner endpoint shifts the two progression indices by amounts differing by $m$. If the partner side contains fewer than the $m+1$ smaller-factor positions, the number of possible sums is zero. We can drop the entire progression. A public inequality also identifies blocks in which every progression has a possible sum, so the evaluator can skip pricing those progressions. [Count identity, exclusion and block test](../PrimeFactors/ReciprocalSumLanes.lean)

We tested eight fresh 38–42-bit products, using blocks of 840 integers and the same wheel of 210. All four searches below recovered all eight pairs, which Lean verified. The public block test avoided pricing 1,520 of 2,815 blocks. [Data and input-generation rule](../research/reciprocal-sum-lanes.json) · [Search and replay](../experiments/reciprocal_sum_lanes.py)

| Complete search on the eight inputs | Candidate factors multiplied |
|---|---:|
| Ordinary smaller-factor interval, counting the retained wheel positions | 539,581 |
| Cheaper partner side for the entire block | 539,518 |
| Cheaper partner side using each progression's actual endpoints | 506,351 |
| Drop every progression with no possible sum | 407,396 |

The last approach removed 24.5% of the ordinary positions. Its 62,119 progression checks still required 124,238 endpoint divisions. In one run it took 0.145 seconds of CPU time, against 0.115 seconds for the existing batched smaller-factor search. A wheel-sieved Fermat search that tried the sums directly found all eight using 19 integer square roots. Even exhausting the same sum range after each hit required only 464 square roots and 0.028 seconds in total. The counts are reproducible. Elapsed times depend on the machine.

## A guarantee near the square root

The top portion of the search interval has a stronger guarantee on **every** odd product coprime to 211. Consider blocks of 844 consecutive integers lying between $0.98\sqrt N$ and $\sqrt N$. Ordinarily 420 positions in such a block are odd and coprime to 211. **At most 36** can survive the factor-sum test, and it retains the true smaller factor whenever the block contains it.

For a candidate $x$ dividing $N$, the sum is $x+N/x$. Near $\sqrt N$ this function changes slowly enough that there are at most 35 possible integer sums in one block. Odd factors also satisfy $p+q\equiv N+1\pmod4$, leaving at most nine sums. For each sum $S$, a lookup in a table of 211 entries gives at most two solutions of $x(S-x)=N\pmod{211}$. Each solution occurs at most twice at an odd position in the block. This gives the bound $9\times2\times2=36$, and supplies the surviving positions without scanning the original 420. Equivalently, the square roots of $S^2-4N$ give the two solutions directly. [Lean coverage and position bounds](../PrimeFactors/ReciprocalSumSlice.lean) · [Evaluator](../experiments/reciprocal_sum_slice.py)

The disjoint complete blocks nearest the square root remove **more than 6% of all** odd positions coprime to 211 in $[\lceil\sqrt{N/2}\rceil,\lfloor\sqrt N\rfloor]$ for every target product. This is the entire range supplied by knowing that the larger prime is at most twice the smaller. Each complete block removes at least 384 candidates, and there are at least $\lfloor\lfloor\sqrt N\rfloor/42200\rfloor$ such blocks. Enumerating that many blocks would itself take far too long. [Full-input count and soundness](../PrimeFactors/ReciprocalSumSlice.lean)

Exhausting **this portion** of the interval on the same eight products took 819 table lookups and 1,630 candidate multiplications, down from 80,214 odd positions coprime to 211. Four smaller primes lay inside the portion, and both the product test and direct Fermat comparison recovered all four. The other four lay outside. Direct Fermat required 409 integer square roots across the eight inputs after the table lookup. [Slice results](../research/reciprocal-sum-slice.json)

On each 2,048-bit input we examined the first two blocks near $0.98\sqrt N$. Of the 840 ordinary candidate positions, 40 survived on the fresh input and 16 on the crossed input. Each interval had 17 possible factor sums. Lean checked all 17 discriminants against consecutive squares and excluded **every divisor** in those 1,688 positions on each input. The last two blocks near $\sqrt N$ admitted no sum even before applying the wheel. Both inputs have more than $10^{300}$ blocks in this portion alone, and neither factorization was recovered. [Full-size fixtures](../benchmarks/reciprocal-sum-slice.json) · [Interval exclusion theorem](../PrimeFactors/SumIntervalExclusion.lean)
