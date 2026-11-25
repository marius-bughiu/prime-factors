# Allocating weighted-sum windows between neighboring slopes

On the two 89-bit inputs, moving the boundaries between neighboring fractions and removing redundant fractions cut the number of giant collision records by about 25%. The same change sped up one 89-bit search and slowed down the other. Both used only the product, the promise of two balanced primes, and the same baby-step count and base as the original search. [Measurements](../research/farey-allocation.json) · [Original search and assumptions](farey-weighted-sums.md)

## What each boundary certifies

Let $N=pq$ with distinct primes $3<p<q\le 2p$. At the unknown ratio $r=q/p$, a reduced slope $a/b$ estimates the integer $t=ap+bq$. It satisfies $t=\sqrt{N/r}(a+br)$. This expression is smallest at $r=a/b$. Starting at $\lceil 2\sqrt{abN}\rceil$, take the first integer $S$ congruent to $a+bN$ modulo $s=\gcd(24,2(a+bN))$. A window of $L$ labels includes $S,S+s,\ldots,S+(L-1)s$. Its first omitted label is $T=S+Ls$. A zero-length window can certify a region in which the ratio cannot occur, since the true sum would have to lie below the first admissible label. [Weighted stride](../PrimeFactors/WeightedStride.lean)

Give each retained slope a closed cell with rational endpoints, containing its center $a/b$. For each endpoint $A/B$, check the integer inequality

$$N(aB+bA)^2 < ABT^2.$$

If the unknown ratio belongs to the cell, then $t<T$ and the window includes it. To verify the claim, subtract $(ap+bq)^2AB$ from $N(aB+bA)^2$. This difference equals $(Ap-Bq)(b^2 A q-a^2 Bp)$. Both factors are nonnegative when the endpoint is to the right of the true ratio and the true ratio is to the right of the center. Both are nonpositive on the other side. Lean checks the resulting bound for every pair of rational endpoints and integer factors. Thus the coverage certificate does not depend on trusting the optimization procedure. [Lean cell certificate](../PrimeFactors/FareyAllocation.lean) · [Independent integer checks](../experiments/farey_allocation.py)

## Which neighboring budgets meet?

Suppose $a/b<c/d$, and let $T,U$ be the first omitted labels at the two centers. As the boundary moves from the left center to the right, the ratio of the left sum to $T$ increases and that of the right sum to $U$ decreases. The best boundary for these fixed budgets minimizes the larger ratio. If the two ratios cross in the interior, cancel their common factor $\sqrt{N/r}$. The crossing is the rational number

$$r=\frac{cT-aU}{bU-dT}.$$

At this cut both upper tests hold precisely when $(cT-aU)(bU-dT)>N(bc-ad)^2$. If the ratios do not cross inside the gap, test the endpoint at which the larger ratio is smallest. The formulas apply even when intermediate Farey slopes are skipped. Equality at a first omitted label fails the test. [Cut identity](../PrimeFactors/FareyAllocation.lean)

To price a giant block, let $m$ be the number of baby powers in the original collision search. Assigning $g$ giant blocks to a slope gives $T=S+sgm$. For an exact comparison, the dynamic program permits up to $h-1$ omitted centers between consecutive retained slopes and always retains the two endpoints of $[1,2]$. Its state is the final slope and its integer block count. A preceding state is compatible precisely when the neighboring windows meet. Taking the cheapest compatible predecessor minimizes total blocks, with number of retained slopes breaking ties. The proved Lean statement certifies coverage. The search optimum within this class follows from this finite recurrence and is separately compared with exhaustive choices on a small instance. [Allocation and tests](../tests/test_farey_allocation.py)

The state space has a finite local bound. Let $G_i$ be the block counts of the ordinary mediant schedule for the full ordered list. A retained center $i$ in a minimum-block plan has $g_i\le\sum_{|j-i|\le h}G_j$. Otherwise replace the plan from its previous retained center through its next retained center with all original centers and their baseline blocks, raising each endpoint to the larger of its original and baseline budgets. The omitted gaps are restored, the two external gaps keep their coverage, and the replacement strictly decreases the total cost. At the ends of the chain use the available one-sided neighborhood. Because compatibility is monotone in each block count, the implementation uses suffix minima to price a compatible predecessor. The total work is $O(h^2G+hK^2)$ arithmetic operations for $G=\sum_iG_i$ and Farey order $K$, with explicit caps on centers, states and transitions. Arithmetic involves integers of $O(\log N+\log K+\log m)$ bits for these schedules.

For the timing comparison we used a cheaper two-pass planner. Start at a weighted mediant, giving the cheaper, larger-stride slope more of the neighboring gap using integer weights $\lfloor10\sqrt s\rfloor$. Try dropping each middle slope and reallocating its blocks to either neighbor. Accept the removal if it preserves coverage without increasing the total block count, shrink the surviving budgets to their required sizes, and reverse direction for the second pass. Both planners finish by returning rational boundaries and the exact label counts. The cheaper planner uses $O(K^2)$ arithmetic operations and enumerates only reduced slopes. [Reproduction harness](../experiments/farey_allocation_comparison.py)

## Complete searches on four products

Each row compares the same public $N,K,m$ and stride-24 collision engine. Center counts in the allocated column are the retained centers after visiting every primitive Farey slope. Raw baseline visits also include unreduced numerator/denominator pairs. Search times are medians of three trials and include planning. The last column separately times checking all endpoint inequalities once. Lean also verified the two prime factors and their product for all four allocated-search outputs.

| Input | Ordinary visits / primitive | Retained centers | Giants ordinary → allocated | Labels ordinary → allocated | Median time ordinary → allocated | Allocated certificate check |
|---|---:|---:|---:|---:|---:|---:|
| previous-63 | 779 / 451 | 270 | 1,299 → 991 | 1,503,044 → 1,314,591 | 0.022 → 0.018 s | 0.7 ms |
| previous-79 | 7,139 / 4,259 | 2,450 | 12,439 → 9,392 | 143,126,963 → 124,126,727 | 0.322 → 0.257 s | 6.3 ms |
| fresh-89-A | 27,027 / 16,275 | 9,389 | 47,323 → 35,344 | 2,074,627,750 → 1,779,029,570 | 1.402 → 1.140 s | 24.9 ms |
| fresh-89-B | 26,795 / 16,155 | 9,366 | 46,977 → 35,034 | 2,048,856,033 → 1,757,572,510 | 0.229 → 0.284 s | 23.9 ms |

The gap-three dynamic program, which can skip up to two consecutive original centers, reached 947, 9,131, 34,264 and 34,042 giants respectively. It minimizes giants for this particular family of center-containing cells, maximum gap and fixed baby table. The timing table uses the cheaper planner. Its 89-bit setup cost matters when a full modular equality returns a factor before polynomial evaluation. These measurements reduce constant factors at fixed table sizes. The exponent remains unchanged. [Median timings, individual runs, label counts and exact-plan counts](../research/farey-allocation.json)

Run the four public cases with the following command. The harness uses the existing collision search with two record builders. It reads only the products and public schedule settings, checks each output divides its product, and verifies the coverage certificate without factor hints.

```sh
python3 -m experiments.farey_allocation_comparison --repetitions 3
```
