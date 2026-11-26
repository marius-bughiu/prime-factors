# What can 33 million weighted rows reach at 2,048 bits?

Fewer than **one in $2^{60}$** eligible products can reveal a factor by a square relation among the first 4,096 admissible labels on **each side** of each of 4,096 weighted endpoints. This allows up to 33,554,432 rows per input, either gcd sign, and every subset of the rows. It also counts factors exposed directly by a label gcd. The bound applies even if choosing the best subset costs nothing. The numerator counts products that could succeed anywhere in the menu. These are finite upper bounds from integer arithmetic and a written proof. [Reproducible calculation](../experiments/weighted_subset_budget.py) · [Growing-menu argument](growing-weighted-square-menus.md)

Let $X=2^{1023}$. Eligible products are $N=pq$ for distinct primes $X\le p<q<2X$ with $N\ge2X^2$. The repository proves that the number of these products exceeds $X^2/21{,}000{,}000$. At weight $1\le r\le K$ set $s_r=\gcd(24,2(r+N))$. Labels $A$ are positive integers congruent to $r+N\bmod s_r$ near $2\sqrt{rN}$. The first $J$ above and first $J$ below that endpoint all satisfy $|A-2\sqrt{rN}|\le Js_r\le H=24J$. A relation uses an exact square product of the signed excesses $D=A^2-4rN$, then takes the gcd of $N$ with the product of labels plus or minus the integer root. A search may choose any weights, labels or subsets from the stated ranges using the entire input. [Population theorem](../PrimeFactors/ChebyshevPrimeSample.lean) · [Admissible progression](../experiments/weighted_square_pairs.py)

| $K=J$ | Rows per input, both sides | Cell width | Support bits $B$ | Rankin exponent $\theta$ | Upper exponent for possible $\lvert D\rvert$ values at one anchor | Successful fraction below |
|---:|---:|---:|---:|---:|---:|---:|
| 16 | 512 | 4 | 642,914 | 36/64 | 693 | $2^{-294}$ |
| 64 | 8,192 | 8 | 10,168,464 | 43/64 | 783 | $2^{-201}$ |
| 256 | 131,072 | 16 | 162,721,256 | 47/64 | 842 | $2^{-139}$ |
| 1,024 | 2,097,152 | 32 | 2,612,841,637 | 50/64 | 884 | $2^{-94}$ |
| 4,096 | 33,554,432 | 64 | 41,990,647,392 | 52/64 | 915 | $2^{-60}$ |

## Fixing the catalogue before counting products

Put $h=\lceil\sqrt K\rceil$ and $w=\max(1,\lfloor J/h\rfloor)$. Partition $[X,2X)$, the range of $\sqrt N$, into $\lceil X/w\rceil$ half-open intervals starting at $X$. Also fix $\rho=N\bmod24$, one of eight unit residues. For a cell with left endpoint $v$ the entire interval of possible labels at weight $r$ lies in

$$[2\sqrt r\,v-Js_r,\,2\sqrt r\,(v+w)+Js_r],\qquad s_r=\gcd(24,2(r+\rho)).$$

Take **all** congruent integers in this interval as the cell's catalogue. It includes labels from every product in that cell and residue class and is fixed independently of the particular product. An interval of length $b$ contains at most $1+\lfloor b/s_r\rfloor$ integers of one residue class. Define

$$L_\rho=\sum_{r=1}^K\left(2J+1+\left\lfloor2\sqrt r\,w/s_r\right\rfloor\right),\qquad P=\lceil X/w\rceil\sum_\rho L_\rho.$$

Thus $P$ gives an upper bound on the number of choices of a catalogue and one anchor row. It includes the cost in the counting argument of conditioning on the residue. It never multiplies the independent numbers of possible labels at successive weights.

For an actual selected label, $|D|\le Y=H(8Xh+H)$. For any catalogue label, including unused ones, $|A-2\sqrt r\,v|\le F=H+2hw$ and $|A^2-4rv^2|\le F(8Xh+F)$. Every determinant $|sA^2-rA'^2|$ between weights $r,s$ is consequently at most $C=2KF(8Xh+F)$ by cancellation of $4rsv^2$. Fix the catalogue and anchor. Form $M$ as the product of all *nonzero* determinants against that anchor, or 1 if none exist. Then $\log_2 M\le B=(\max_\rho L_\rho-1)\lceil\log_2 C\rceil$. Both the anchor and $M$ remain fixed while counting $N$. The calculation uses this bit bound without constructing a forty-billion-bit product. [Cell geometry, catalogue counts and determinant bounds in Lean](../PrimeFactors/WeightedGrowingCells.lean)

In every row of the table $24J<2X$, so even the lowest allowed label is positive. All weights are below $X$, so $4rN$ has an odd valuation at both $p$ and $q$ and each actual excess is nonzero. Suppose all participating labels are units modulo $N$. For proportional rows $sA^2=rA'^2$, the signed integer $A'D/A$ is a square root of the product of the two excesses and is congruent to $AA'\bmod N$. It is integral since its square is an integer. Removing such pairs preserves the square condition and whether either gcd is proper. Indeed the remaining integer product then has a rational square root, hence an integer one. An empty reduced relation has only the gcds $N$ and $1$. Every splitting relation therefore has a nonempty representative with no proportional pair. [Signed cancellation and squarefree support in Lean](../PrimeFactors/WeightedSignedSupport.lean)

Choose an anchor of the reduced relation. Every prime occurring to odd order in $|D|$ must divide another excess in the relation. It therefore divides their nonzero determinant and divides $M$. Consequently $|D|=mu^2$ with squarefree $m\mid M$. A particular $|D|$ permits at most two products $N$ at the anchor, one per sign. For $1/2\le\theta<1$ the number of possible positive magnitudes is at most

$$Y^\theta\prod_{\ell\mid M}(1+\ell^{-\theta}).$$

This follows by bounding $\lfloor\sqrt{Y/m}\rfloor$ by $(Y/m)^\theta$ for $m\le Y$, then summing over squarefree divisors. It covers every reduced subset containing the anchor in one count. [Finite support across subsets](../PrimeFactors/WeightedTripleSupport.lean) · [Lean bound for every real exponent at least one half, including both signs](../PrimeFactors/WeightedSubsetRankin.lean)

## An integer certificate for the Euler product

Each distinct prime divisor in $[2^j,2^{j+1})$ costs at least $j$ of the $B$ support bits. Split each such interval into subintervals of integer width $\max(1,2^j/16)$. Below 65,536 count primes exactly by Eratosthenes. In larger subintervals count integers coprime to $30{,}030=2\cdot3\cdot5\cdot7\cdot11\cdot13$ by complete periods and the partial period. Every prime there is included. Additionally impose the whole-interval cap $\lfloor2^{j+1}/j\rfloor$. Every prime between $2^j$ and $2^{j+1}$ divides $\binom{2^{j+1}}{2^j}\le2^{2^{j+1}}$. Both endpoints are composite in these larger intervals. [Counting wheel residues in Lean](../PrimeFactors/WeightedPrimeBins.lean) · [Dyadic cap and Euler-product estimates in Lean](../PrimeFactors/WeightedPrimeBudget.lean)

Fill the available subinterval positions from the smallest lower endpoint $a$ upward, subject to the whole-interval cap and the total bit budget. This dominates **every** feasible ordered prime support. Within an interval, the earliest permitted positions meet or exceed every true prefix count up to the whole-interval cap. Concatenating those lists gives a sequence whose $i$th entry is at most the $i$th actual prime. These earliest entries also have no greater support-bit price. Truncating when the next entry is unaffordable therefore still leaves at least as many entries as any feasible support. If $n_a$ positions are filled at a lower endpoint $a$, the Euler-product correction satisfies

$$\log_2\prod_{\ell\mid M}(1+\ell^{-\theta})\le \log_2(e)\sum_a n_a a^{-\theta}.$$

The script tests $\theta=k/64$, $32\le k\le63$. It rounds each $a^{-k/64}$ **up** to a multiple of $2^{-80}$ using six integer square roots of $\lfloor2^{5120}/a^k\rfloor$ and an exact equality test. It uses $\log_2(e)<1443/1000$, verified by four positive terms of $\log 2=2\sum_{i\ge0}3^{-(2i+1)}/(2i+1)$. Adding $\theta\lceil\log_2Y\rceil$, taking the best bound and rounding upward gives the table's fixed-anchor exponent $f$. All unit-label successes together number at most $2P\,2^f$.

Finally, if either prime $p$ divides a label, write $A=cp$. There are at most $X$ possible integers $p$ in the prime interval, at most $4h+\lfloor H/X\rfloor$ positive values of $c$, and $K$ possible weights. The signed integer $e=D/p$ has $|e|\le\lfloor Y/X\rfloor$. Those data determine the other prime by $q=(c^2p-e)/(4r)$. Counting $p$ over the entire interval covers both orientations. Adding this count to the unit-label bound and dividing by the proven population gives the strict savings in the table. [Prime-population denominator](../PrimeFactors/ChebyshevPrimeSample.lean)

Run `python3 -m experiments.weighted_subset_budget` to reproduce every row and the intermediate bit budgets, residue-class catalogue sizes and rounded corrections. A second calculation uses rational prices for the support bits and prime-count limits, trial division for small primes, and an independent integer-power check for each rounded term. Run `python3 -m experiments.weighted_subset_budget_dual` to check all five bounds this way. [Independent verifier](../experiments/weighted_subset_budget_dual.py)

Lean checks the catalogue geometry, signed cancellation, the count for a fixed row, and prime-bin estimates. The five numerical rows combine those steps in a written proof with exact integer arithmetic. An end-to-end Lean theorem for the numerical table remains open. The 16-row fixed-menu theorem is separately kernel-checked. [Lean finite-menu count](../PrimeFactors/WeightedSubsetPopulation.lean)
