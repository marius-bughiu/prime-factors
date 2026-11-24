# Optimal coverage for a prescribed midpoint-test budget

Choose two distinct primes uniformly without replacement in $[X,2X)$ and write them in order as $p<q$. Fix a list of moduli and search depths *before* seeing $N=pq$. At modulus $1\le m<X$, test the first $B_m$ midpoints starting at $r=\lceil\sqrt N\rceil$ in each root class of $h^2\equiv N\pmod{m^2}$. Count a success only when a midpoint gives the two nontrivial factors.

Let $R(m)$ count the square roots of one modulo $m^2$, with $R(1)=1$. A list reserves $\sum_mR(m)B_m$ midpoint tests. For any fixed $0<\epsilon<1/2$ and every integer budget $1\le T\le X^{1/2-\epsilon}$, the largest success probability among lists reserving at most $T$ tests is

$$
  \Theta_\epsilon\!\left(\frac{T}{\sqrt X}\right).
$$

The constants are uniform in $T$ for sufficiently large $X$ depending on $\epsilon$. The upper bound $O(\min\{1,T/\sqrt X\})$ holds for every budget. The estimate is unconditional. It is a paper deduction from prime counting and the midpoint arithmetic checked in Lean. [Formal search and exclusion](../PrimeFactors/GapStride.lean) · [Prime-pair counting argument](gap-search-frequency.md)

## Why every prescribed list obeys the upper bound

Put $D=(q-p)/2$ and $H=(p+q)/2$. For $B_m\ge1$, the entry at $m$ finds the pair exactly when $m\mid D$ and $H-r<B_m m^2$. The congruence is equivalent to $m^2\mid D^2$. The inequality says that $H$ is among the first $B_m$ representatives of its class. The Lean theorems `budget_gap_root_iff` and `gap_stride_necessary` check this equivalence and the squared-gap bound below. On a hit, integrality gives $H-\sqrt N<B_m m^2$. Since $H+\sqrt N<4X$,

$$
   D^2=(H-\sqrt N)(H+\sqrt N)<4XB_m m^2.
$$

For each prime $p$, all possible partners therefore lie in a single reduced class $q\equiv p\bmod 2m$ in an interval of length $4m\sqrt{XB_m}$. The short-interval Brun–Titchmarsh inequality gives at most $O((m/\varphi(m))\sqrt{XB_m}/\log X)$ primes there. Indeed the length divided by the modulus is $2\sqrt{XB_m}$, and $2m/\varphi(2m)\le2m/\varphi(m)$. These bounds are uniform even when this interval extends beyond the sample. The prime number theorem gives $P\asymp X/\log X$ choices for the first prime. Dividing the pair count by $\binom P2$ bounds success at this entry by $O((m/\varphi(m))\sqrt{B_m/X})$. [Montgomery and Vaughan, *The large sieve*, Theorem 2](https://doi.org/10.1112/S0025579300004708)

Since $m<X$, $N$ is a unit modulo $m^2$. Whenever a root exists, multiplication by it gives a bijection between the roots of one and the roots of $N$. At each prime power dividing $m^2$ there are at least two roots of one, given by $\pm1$. Even for a factor of two the component modulus is at least four. CRT therefore gives $R(m)\ge\prod_{\ell\mid m,\ \ell\text{ prime}}\ell/(\ell-1)=m/\varphi(m)$. Sum the preceding probability bound and use $\sqrt{B_m}\le B_m$ for each positive integer depth. Moduli with zero depth contribute zero. This proves the bound for composite moduli, prime powers, and lists with repeated entries.

## An explicit bound at exactly 2048 bits

Set $X=2^{1023}$. Sample a uniform unordered pair of distinct 1024-bit primes, conditioned on its product having **exactly 2048 bits**. For every prescribed list in this model, its probability of success is less than

$$1024\,T/\sqrt X$$

when $T>0$. For example, even $2^{40}$ reserved midpoint slots succeed on less than a $2^{-461}$ fraction. A success probability of one half would require **more than $2^{500}$ reserved slots**. This is a finite upper bound at the requested size. It does not extend to searches that choose their moduli or offsets from the observed digits of the product.

Here are the constants. Let $U=X/\log X$, let $P$ count the primes in $[X,2X)$, and let $P_*$ count those in $[\sqrt2X,2X)$. Every pair of distinct primes in the latter interval has a 2048-bit product. The explicit bounds $t/\log t<\pi(t)<1.25506t/\log t$ for $t\ge17$ imply $P<1.511U$ and $P_*-1>0.22U$. For the first inequality subtract the lower bound at $X$ from the upper bound at $2X$. For the second, $\log X/\log(2X)=1023/1024$ and $\sqrt2<1.415$, giving $P_*/U>2(1023/1024)-1.25506(1.415)>0.222$. At this $X$, $U>1000$, so subtracting one preserves the stated bound. [Rosser and Schoenfeld, Corollary 1, inequalities (3.5)–(3.6)](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6)

For each first prime and each positive depth $B_m$, Brun–Titchmarsh with length $4m\sqrt{XB_m}$ and modulus $2m$ bounds the partner count by $16(m/\varphi(m))\sqrt{XB_m}/\log X$. Summing over the list and all $P$ first primes gives at most $16PTU/\sqrt X$ successful unordered pairs before imposing the bit-length condition. The conditional population has at least $P_*(P_*-1)/2$ pairs. Dividing gives the displayed bound since $32(1.511)/(0.22)^2<1024$. The cited analytic inequalities enter on paper; the necessary gap inequality is machine checked. [Montgomery and Vaughan, Theorem 2, equation (1.10)](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3) · [Lean proof](../PrimeFactors/GapStride.lean)

## A list that attains the bound

For $T=1$, take $m=1$ and one midpoint. Its coverage is $\Theta(1/\sqrt X)$ by the short-gap count. For $T\ge2$ put $k=\lfloor T/2\rfloor$ and $Z=C_\epsilon T\log(2T)$. Select any $k$ primes $m\equiv3\pmod4$ in $[Z,2Z]$, using one midpoint per root. Taking $C_\epsilon$ sufficiently large supplies $k$ primes uniformly for $T\ge2$ by the prime number theorem modulo four. Each chosen prime has $R(m)=2$. The list reserves $2k\le T$ slots. [One-test criterion and prime-band construction](gap-search-frequency.md)

Write $Y=\lfloor\sqrt X\rfloor$. For each selected $m$, divide the population into successive bins of length $2mY$ and then into residue classes modulo $2m$. The number of boxes is $O(X/Y)$ uniformly, since $m\le2Z\le X^{1/2-\epsilon/2}$ for all sufficiently large $X$. By Cauchy–Schwarz the number of distinct unordered prime pairs sharing a box is at least $(P^2/\#\mathrm{boxes}-P)/2\gg XY/\log^2 X$. All have $m\mid D$ and $D/m\le Y$, which implies $H-r<m^2$.

For another selected prime $m'$, pairs in this count with $m'\mid D$ satisfy $q\equiv p\bmod 2mm'$ and $0<q-p\le2mY$. Brun–Titchmarsh counts at most $O_\epsilon(XY/(m'\log^2 X))$ such pairs, since $\log(Y/m')\gg_\epsilon\log X$. The implied constant can be fixed before choosing $C_\epsilon$ by taking $X$ sufficiently large after that choice. Over the other selected primes, $\sum 1/m'\le k/Z\le1/(2C_\epsilon\log(2T))$. Choose $C_\epsilon$ large enough that deleting all these overlaps costs at most half the single-modulus lower bound. The remaining sets are disjoint. Summing over $k\asymp T$ primes and normalizing by $\binom P2$ proves the claimed lower bound.

## Which resource is optimized?

The budget reserves every possible root slot in advance. On a particular input, some moduli have no roots and early successes can save work. Computing roots, building the prime list and testing a midpoint each take time. For the attaining list, a sieve constructs the primes and modular exponentiation gives a candidate root at each prime $m\equiv3\pmod4$. A single Hensel lift per root gives its value modulo $m^2$. These steps take $T(\log X)^{O(1)}$ bit operations, including square testing, at the stated budgets. [Root algorithm and cost](gap-search-frequency.md)

The list may depend on the public population scale $X$ and the budget. For equal-bit-length prime pairs the dyadic scale $X$ is determined by the input width as described in the frequency proof. The theorem covers the first consecutive representatives of every root class. Selecting moduli from product-dependent observations, choosing other offsets, and reassigning unused slots adaptively require separate analysis. Near and above $T=\sqrt X$ only the upper bound here applies. Recovering general 2048-bit factors efficiently remains open. [Earlier coverage comparisons](gap-search-frequency.md)
