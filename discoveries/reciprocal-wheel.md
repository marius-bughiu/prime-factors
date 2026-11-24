# Can remainders tell us which factor to test?

Suppose $N=pq$ with unknown distinct odd primes $p<q\le2p$. Knowing $p\bmod W$ determines $q\bmod W$ whenever $\gcd(W,N)=1$. We can use that relation to retain the smallest possible set of candidates consistent with a rectangular pair of intervals and a wheel. On a 41-bit example it removed about 80% of the ordinary wheel candidates. The extra grouping made the complete search about eight times slower. For **every 2,048-bit input** in this class, any wheel $W\le2^{1020}$ permits **zero savings from swapping sides on the whole balanced interval**. Shorter subdivisions can save candidates. [Lean bounds](../PrimeFactors/ReciprocalWheel.lean) · [Reproducible implementation](../experiments/reciprocal_wheel.py)

## The optimal choice in a rectangle

Take a block of possible smaller factors $I=[a,b]\cap\mathbb Z$, with $1\le a\le b\le\lfloor\sqrt N\rfloor$. Its companion block is $J=[N/b,N/a]\cap\mathbb Z$. For each unit residue $r\bmod W$ define $s=\sigma(r)=Nr^{-1}\bmod W$. The map $\sigma$ is an involution. Write $I_r,J_s$ for the integers of the respective residues, with counts $l_r,h_s$. The local candidates are precisely the edges of the disjoint complete bipartite graphs $I_r\times J_{\sigma(r)}$. These edges are all the *local* product possibilities. Full integer equality $xy=N$ is used later.

A set of integers meeting every edge in a component must include all of $I_r$ or all of $J_{\sigma(r)}$. Otherwise a missed vertex on each side gives a missed edge. Thus the minimum number of tested integers across the rectangle is exactly
$$
S_*=\sum_{r\in(\mathbb Z/W)^\times}\min(l_r,h_{\sigma(r)}).
$$
Choose the cheaper entire side of each component, taking the smaller-factor side in a tie. This includes exactly one endpoint of every actual pair. For a partition into disjoint smaller-factor blocks, genuine partners also occur only in the corresponding upper block. Throughout the complete balanced band all candidate integers are below $2p$, since $q<2p$ for distinct odd primes and the upper endpoint is at most $\sqrt{2N}$. A single gcd of the selected product with $N$ therefore returns precisely one prime, and division gives the other. The implemented width-limited choice always selects the smaller factor. [Formal cover optimality](../PrimeFactors/ReciprocalWheel.lean)

Choosing one residue for both intervals on each two-cycle is a more restrictive rule. For the orbit $\{r,s\}$ it incurs the smaller of $l_r+h_r$ and $l_s+h_s$. The unrestricted optimum also considers both lower lanes and both upper lanes. In a fixed class $r=\sigma(r)$ both factors have the same residue. Searching it over both intervals can include **both** primes. Choosing just its cheaper side preserves the single-factor gcd. This explains why simply halving the residues does not automatically halve the search.

## Exact tradeoff with interval size

A lane on a consecutive interval with $m$ sites has $\lfloor m/W\rfloor$ or $\lceil m/W\rceil$ members. Put $A=|I|$ and $B=|J|$. If $\lfloor A/W\rfloor<\lfloor B/W\rfloor$, the lower lane is always cheapest. The opposite strict inequality makes the upper lane cheapest. If both floors equal $h$, write $E_I,E_J$ for the cyclic intervals of residues represented once more than $h$ times. Then
$$
S_*=h\varphi(W)+\#\{r\text{ unit}: r\in E_I,\ \sigma(r)\in E_J\}.
$$
The correction is an exact rectangle query on the modular inverse permutation. It treats endpoints even when one interval contains no integers.

The real companion span is
$$
N/a-N/b=(b-a)+\frac{(b-a)(N-ab)}{ab}.
$$
Thus $B\ge A-1$ and an upper lane can save at most **one integer per residue per block**. If $(b-a)(N-ab)\ge Wab$, then $B\ge A+W-1$ and no upper lane can save anything. In particular $(b-a)^2\ge Wa$ suffices because $N\ge b^2$. For the entire 2,048-bit band take $a=\lceil\sqrt{N/2}\rceil$ and $b=\lfloor\sqrt N\rfloor$. Then $a\ge2^{1023}$, $2(a-1)^2\le N<(b+1)^2$, and these inequalities imply $(b-a)^2\ge2^{1020}a$. This finite cutoff uses the full interval supplied by the balance promise. If additional size information gives a narrower interval, the local endpoint inequality applies to that interval. [Lean rounding, width and finite-size proof](../PrimeFactors/ReciprocalWheel.lean)

For $K$ paired blocks let $S_0$ count all lower wheel candidates and $S_*$ the summed optimum. Then $S_0-S_*\le K\varphi(W)$. If a method explicitly prices $f=\varphi(W)$ residues and $K$ blocks, the additive count satisfies
$$
f+K+2\sqrt{S_*}\ge2\sqrt{S_0}.
$$
This follows from $fK\ge S_0-S_*$ and the arithmetic-geometric mean inequality. It bounds that particular accounting of residue enumeration, block visits and square-root batching. Reused preprocessing or a method using additional information may have different costs. [Checked cost inequality](../PrimeFactors/ReciprocalWheel.lean)

## Computing the pruned product without listing its factors

Use blocks with at most $W$ integers. Now $l_r$ is zero or one. The optimum is attained by retaining precisely those lower candidates whose partner residue occurs at least once in $J$. All skipped components have an empty upper lane. A lower block splits at a wheel boundary into at most two pieces, each with $x=kW+r$ for fixed $k$. The allowed partner residues form a full period or at most two half-open residue intervals. These choices give at most four rectangles per block in the $(r,\sigma(r))$ plane.

Use a binary subdivision on each coordinate from zero up to the smallest power of two at least $W$. Each rectangle splits into $O(\log^2(2W))$ disjoint pairs of tree nodes. For each queried pair $v$, collect its unit residues $R_v$ and form the polynomial
$$
F_v(Z)=\prod_{r\in R_v}(Z+r)\pmod N.
$$
Every query for this pair asks for $F_v(kW)$. Group the queries by $v$ and use monic multipoint evaluation, which works over the composite modulus. The selected rectangles are disjoint within each lower block, and different lower blocks contain different integers. Multiplying the evaluations therefore gives the precise pruned product, with each retained integer occurring once. The tests compare the full modular value to independent scalar enumeration, as well as checking the factor. [Implementation](../experiments/reciprocal_wheel.py) · [Cross-checks](../tests/test_reciprocal_wheel.py)

The wheel enumerates $W$ slots by gcd and inverts each of its $f$ units. Each unit belongs to $O(\log^2(2W))$ node pairs. Their total polynomial degree is $O(f\log^2(2W))$. The number of scheduled evaluations is $O(K\log^2(2W))$. With fast polynomial multiplication these cost $\widetilde O(f+K)$ modular coefficient operations. Including the gcds, inversions, division to locate intervals, and tree bookkeeping gives $\widetilde O((W+K+1)\log(2N))$ bit operations for $W,K\le N$. Deterministic sorted grouping can replace dictionary lookups at logarithmic cost. This asymptotic bound assumes fast integer arithmetic. The reference uses the repository's packed Python integer polynomial backend. Orthogonal range searching and product/remainder trees are established techniques. [Bentley on decomposable searching](https://www.sciencedirect.com/science/article/abs/pii/0020019079901170) · [Earlier one-dimensional batched progression product](batch-intervals.md)

For the **ordinary** lower product, each such block also has at most $W$ entries, so one residue tree suffices for the same soft bound. More generally $S_0\le Kf$ in this regime, and the earlier $\widetilde O(W+K+\sqrt{S_0})$ bound already has this order. For the full band, $K$ is at least its width divided by $W$. Minimizing $W+K$ again gives fourth-root order in $N$. The grouped construction produces the stronger filtered product within that order. Timing comparisons should include its larger setup and evaluation counts. [Earlier prime-modulus filter and its scope](hyperbola-boxes.md) · [Costa and Harvey on faster wheel-based factoring](https://arxiv.org/abs/1201.2116)

## Complete searches

At $N=15{,}049$, wheel 30 and width seven, the six blocks contain ten ordinary candidates. Exactly 91, 97 and 101 survive the paired filter. Their product is 3,636 modulo the input, whose gcd with 15,049 is 101, leaving the prime 149.

For $N=1{,}900{,}014{,}700{,}027$, the ordinary and reciprocal runs below used identical wheels and recovered $1{,}000{,}003$ with one final gcd. The partner is $1{,}900{,}009$. Timings are medians of five local complete runs. Degrees for the reciprocal runs are summed over queried polynomials.

| Wheel | Method | Lower candidates in product | Polynomial degree | Evaluation points | Time |
|---:|---|---:|---:|---:|---:|
| 210 | Ordinary wheel | 92,279 | 336 | 273 | 10.9 ms |
| 210 | Paired blocks of 28 | 16,728 | 555 | 16,465 | 137 ms |
| 2,310 | Ordinary wheel | 83,891 | 480 | 174 | 8.8 ms |
| 2,310 | Paired blocks of 330 | 16,908 | 3,001 | 9,639 | 71.4 ms |

The ordinary baseline also multiplied 551 and 371 individual boundary terms respectively. The narrow paired runs visited 14,419 and 1,224 blocks. On the second wheel, increasing the paired width to a full period left 83,808 candidates and required 2,464 evaluation points. These comparisons show how much the residue constraint prunes and how much arithmetic it costs to apply it. [Experiment and ordinary baseline](../experiments/reciprocal_wheel.py)

On the established 2,048-bit control, the bounded run visited the first 16 blocks of width 28 at wheel 210. Those blocks contained 102 ordinary candidates, of which 17 were compatible. The gcd was one and the full cofactor remained unresolved. [Decimal inputs, products and expected outcomes](../benchmarks/reciprocal-wheel.json)
