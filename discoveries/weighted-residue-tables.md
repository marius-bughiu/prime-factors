# Moving forbidden weighted sums into one sparse power table

On the 79-bit comparison input, the ordinary weighted schedule uses 26,363 baby and giant records. Shifting each slope's starting point to share a sparse baby table gives 22,643 records for the same Farey windows. This is a count before deduplicating modular powers. The census does not time a factor search. [Exact counts](../research/weighted-residue-tables.json) · [Implementation](../experiments/weighted_residue_tables.py)

Let $N=pq$, $p<q\le2p$, and suppose $N$ is coprime to the sieve moduli. For primitive weights $1\le b\le K$, $b\le a\le2b$, write $T=ap+bq$, $C=a+bN$ and $s=\gcd(24,2C)$. The published Farey window supplies $[l,h]$, and $T\equiv C\bmod s$ at the true weights. Write $f$ for the first such integer in the window, and $U$ for its number of stride-$s$ sites.

## The cost of separate residue lanes

Modulo an additional prime $\ell\ge5$, the possible trace residues are $au+bN/u$ as $u$ ranges over units. If $\ell\nmid ab$, the involution $u\mapsto bN/(au)$ pairs the two preimages. Its fixed points solve $a u^2=bN$, giving exactly $(\ell+(\frac{abN}{\ell}))/2$ image values. If $\ell\mid ab$, only one coefficient vanishes and the image is all $\ell-1$ units. The prime divisors of $N$ have been excluded by gcd at setup.

For a squarefree product $D$ of extra primes, let $R\subset[0,D)$ consist of indices $i$ for which $f+si$ lies in each local image. Each giant confined to a single lane covers up to $m$ consecutive lane entries. Writing $U=jmD+v$ with $0\le v<mD$, the exact minimum is

$$j|R|+\#\{r\in R:r<v\}.$$

The full blocks visit each lane $m$ times. The remainder needs one further giant on each nonempty lane. Hence a product-only rule can prefer this scheme just on slopes where the count beats $\lceil U/m\rceil$.

There is a limit to that improvement. For every prime $\ell\ge11$, $((\ell-1)/2)^3\ge\ell^2$. The two smaller primes change only the absolute constant, so $|R|\gg D^{2/3}$ for **every** squarefree choice. If $U\ge D$, each lane is visited at least $\lfloor U/D\rfloor$ times. The giant count is therefore $\gg D^{2/3}\max(1,U/(2Dm))\gg(U/m)^{2/3}$. This allows a different wheel on every slope.

Put $X=\sqrt N$. For $K=O(X^{1/5})$, all these windows have $U\gg X/K^3$ for large $N$. Indeed each available Farey side uses a denominator sum $h'\le2K$ and adds at least $\lfloor N/(10K^2)\rfloor$ to $4abN$ under the square root. Taking the difference of square roots divides that gain by $O(bX)$, and the stride is at most 24. There are $\gg K^2$ primitive slopes: the noncoprime pairs in $[1,K]^2$ number at most $K^2\sum_{d\ge2}d^{-2}<0.65K^2$, and symmetry gives the lower triangle. Summing the bound yields $G\gg (X/m)^{2/3}$, hence $m+G\gg N^{1/5}$. For larger $K$ the primitive-slope visits themselves already cost this much. This covers polylogarithmic wheels, and more generally wheels fitting one full period in each window. With larger wheels it also applies if each slope is charged for enumerating its own $|R|$ classes. Sparse oversized queries with reused preprocessing and deduplicated power evaluations are outside this lower bound. [Farey endpoints](../experiments/weighted_windows.py)

## One shared table of permitted baby indices

At a regular prime $\ell\nmid ab$, the residue $T/s$ is permitted exactly when $(T/s)^2-4abN/s^2$ is a square modulo $\ell$, including zero. Choose a public run $z,\ldots,z+k_\ell-1$ missing from that image. At a singular prime $\ell\mid ab$, only zero is missing. For $k_\ell=1$ choose $z=0$. For $2k_\ell\le\ell$ and $k_\ell>1$, offer **two phases** $z=0,k_\ell$. Their runs are disjoint, so every true residue lies outside at least one run.

For each combination of phases, CRT gives $0\le j<D$ satisfying $j\equiv f/s-z\bmod\ell$ at every selected prime. Start at $A=f-sj$. For the true trace, some such phase makes every residue of $(T-A)/s$ avoid $[0,k_\ell)$. Choose a multiple $M$ of $D$ and use the common baby indices

$$\mathcal B=\{0\le i<M:i\bmod\ell\ge k_\ell\text{ at every selected prime}\}.$$

Dividing $(T-A)/s$ by $M$ gives a block and a baby index in $\mathcal B$. One modular power with exponent $(24/s)(C-A-sM\cdot\mathrm{block})$ matches $(\beta^{24})^i$ modulo $p$. The implementation counts only blocks having a permitted index inside the original window, including the two partial ends. Several phases can contain the same true trace. The coverage proof needs at least one, and the counts charge all scheduled phases. [Lean CRT and phase-cover proof](../PrimeFactors/WeightedSparseCoverage.lean) · [Tests including a genuine trace needing the second phase](../tests/test_weighted_residue_tables.py)

## How many records suffice?

Take the primes $5\le\ell\le y$ with $y=(\log N)/16$, and their product $D$. For any fixed $0<c<1/(2\log2)$, the character-sum bound guarantees runs of length $k_\ell=\lfloor c\log\ell\rfloor$ at all sufficiently large regular primes. Use one missed value for the remaining primes. The shared-table density is $\rho=\prod(1-k_\ell/\ell)=y^{-c+o(1)}$, using $\sum_{\ell\le y}\log(\ell)/\ell=\log y+o(\log y)$. [Run proof and finite minima](translated-image-runs.md)

The number of phases for $(a,b)$ is at most $g(a)g(b)$ where $g(v)=2^{\omega_y(v)}$ counts squarefree divisors using the selected primes. For every $u$, summing the divisor indicators gives $\sum_{v\le u} g(v)\le u\prod_{\ell\le y}(1+1/\ell)=O(u\log y)$. Thus $\sum_{b\le K}\sum_{b\le a\le2b}g(a)g(b)=O(K^2(\log y)^2)$. With a factor $1/b$ the same sum is $O(K(\log y)^2)$. This bound accounts for **every** singular slope.

When $M\ge D$, the CRT offset adds at most one block per phase. The upper window bound is $U=O(1+X/(bK^2))$. Therefore there are $\rho M$ babies and

$$G=O\!\left((\log y)^2\left(K^2+\frac{X}{KM}\right)\right)$$

giants. Taking $K$ of order $(\rho X/(\log y)^2)^{1/5}$ and $M$ of order $X/K^3$, rounded up to a multiple of $D=N^{1/16+o(1)}$, bounds total records by

$$O\!\left(N^{1/5}(\log N)^{-2c/5+o(1)}\right).$$

Using just one missing residue at every prime needs one phase per slope and gives $O(N^{1/5}/(\log\log N)^{2/5})$ records. These are gains within the ordinary Farey-weight construction. Harvey and Hittmeir choose a coefficient lattice from the factor residue, and the repo's wide-modulus construction reports a stronger asymptotic bound with those different weights. [Harvey–Hittmeir](https://arxiv.org/abs/2105.11105) · [Wide-modulus result and scope](wide-modulus-sieve.md)

Actual factor searches must pay for generating phases, certifying the powers and evaluating collisions. A sufficient local-order test verifies that all $h^i-1$ for $1\le i<M$ are units, where $h=\beta^{24}$. Its product can be batched by writing $i=jB+k$ with $B\asymp\sqrt M$, evaluating $\prod_{k=1}^{B}(Xh^k-1)$ at powers $h^{jB}$, and handling the tail. A verified proper gcd gives a divisor. A whole-modulus gcd requires refinement or a different verified base. Under a successful order check, a whole-modulus baby/giant equality pins down the only possible local baby index. Every associated phase and window must still test its own valid trace by the quadratic discriminant. Padding outside a window can be discarded for that record. For the remaining entries an arbitrary-point multipoint evaluator can use the actual sparse table. Evaluating a dense chirp through $M$ still charges the missing sites. The record bound alone gives no measured runtime improvement. [Geometric evaluation and collision handling](https://arxiv.org/abs/2010.05450)

## Finite counts

The controls use the established $K$ and dense baby capacity $m$. Each sparse span is $M=D\lfloor m/|\mathcal B\bmod D|\rfloor$. The census uses only $N$ and the public settings. These totals include babies and giants.

| Input | Extra primes | Dense | Sparse | Reduction |
|---|---|---:|---:|---:|
| 63 bits | 5, 7 | 2,705 | 2,380 | 12.0% |
| 79 bits | 5, 7, 11 | 26,363 | 22,643 | 14.1% |
| 99 bits | 5, 7, 11 | 429,810 | 369,099 | 14.1% |

On the 2,048-bit control with $K=32$, both the ordinary and the $5\cdot7$ sparse giant counts have 1,008 bits. These numbers were computed by division over 325 primitive slopes. No such table was allocated and no factor was found. The saved panel also includes both 89-bit products, exact independent-lane minima and the two-phase wheel $5\cdot13$. [Reproducible counts](../research/weighted-residue-tables.json)

## Executing the sparse schedule

The executable found $622{,}358{,}546{,}533$ on the 79-bit product and $20{,}895{,}494{,}959{,}567$ on the first 89-bit product. It checked the order throughout the full spans, 22,330 and 85,085 respectively. It also evaluated the collision polynomial throughout those spans, then took the batch gcd using only the 13,920 and 53,040 retained baby indices. Thus the implementation saves giant records while paying for a longer geometric convolution. On the 2,048-bit product it tested 96 giants against 48 retained indices, evaluated 70 positions, and left $N$ unresolved. A dense search using the same larger span is an additional timing control for the effect of the residue mask itself. [Executable](../experiments/weighted_stride_search.py) · [Search budgets, work and factorizations](../benchmarks/weighted-sparse.json)

We timed three versions in rotating order on the same arm64 Mac. On the 79-bit input the medians were 0.386 seconds with the original dense span, 0.287 seconds with the enlarged dense span and 0.305 seconds with the translated table. On the first 89-bit input they were 1.719, 1.319 and 1.470 seconds. In both comparisons, increasing the span sped up the dense control. The translated implementation used fewer retained records but took longer than that equal-span control. These timings include its dense order checks and dense convolution. [Raw timings, spans and work counts](../research/weighted-sparse-timings.json)

## A finite limit for the measured wheels

A block of span $M$ keeps at least one position $r$. Each consecutive interval of length $M$ includes a position congruent to $r$ modulo $M$, in a separate block. Thus the dense block count at the same span exceeds the shifted nonempty block count by at most one per slope, even charging only one shift. If at least half the positions are kept, $M$ is at most twice the stored baby count. The earlier full-schedule lower bound then gives **more than $2^{403}$ records** for any $K,M$ on a 2,048-bit product in this design. All three wheels in the finite table satisfy that density condition. For the $5\cdot7\cdot11$ wheel, 240 of the 385 positions are kept in each period. This bounds the cost of exhaustive coverage. [Lean proof](../PrimeFactors/SparseFareyWork.lean)
