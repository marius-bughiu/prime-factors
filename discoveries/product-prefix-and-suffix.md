# Choosing midpoint searches with half of the product bits

How much can a lookup table improve a Fermat search if its index comes from the product? Suppose the input is a uniformly sampled pair of distinct 1024-bit primes conditioned on a 2048-bit product. The selector can read **any mixture of the leading and trailing bits up to 1,024 bits in total**, including the known leading one. At every step it can use the bits already read to choose which end to read next. Each resulting table entry can prescribe different moduli and depths. With $2^{40}$ reserved midpoint tests per entry, the success probability is **less than $2^{-441}$**. The table itself can be arbitrarily expensive to train or store. The subsequent square-root and midpoint calculations use the full input. [Earlier bound for a single fixed table entry](stride-budget.md) · [Machine-checked cell injection](../PrimeFactors/ProductAdvice.lean)

## The arithmetic in one table entry

Put $X=2^{1023}$, $D=(q-p)/2$, $H=(p+q)/2$ and $r=\lceil\sqrt N\rceil$. At modulus $1\le m<X$, let $B\ge1$ be the number of initial representatives tested per root of $N$ modulo $m^2$. The underlying Lean theorem says a success requires $D=mc$ with $c^2<4XB$. Thus $1\le c\le C=\lfloor 2\sqrt{XB}\rfloor$. The budget $T$ for an entry counts $R(m)B$ slots for each modulus, where $R(m)$ is the number of square roots of one modulo $m^2$. It follows that $\sum_m\sqrt{B_m}\le T$. [Exact success criterion and converse](../PrimeFactors/GapStride.lean)

After reading $h$ further high bits and $k$ low bits, the product lies in an interval of width $\Delta=2X^2/2^h$ and a residue class $a$ modulo $Q=2^k$. Here $h+k\le1023$, and $a$ is odd for $Q>1$. For $Q=1$ use the odd representative $a=1$ of the only class. Write $W=X/2^{h+k}$, an integer. For a fixed $c$, a first factor $x$ satisfies

$$ (x+mc)^2\equiv a+(mc)^2\pmod Q. $$

For each root on the right there are at most $W$ possible values of $x$. Indeed two candidates with the same $x\bmod Q$ and $(\lfloor x/Q\rfloor\bmod W)$ have difference at least $QW$ if they differ. Their products $x(x+2mc)$ differ by at least $2XQW=\Delta$, so they cannot lie in one half-open interval of that width. The Lean proof injects the entire set of pairs $(c,x)$ into triples consisting of the cofactor, root and index below $W$. It applies to every modulus $Q$. [Cell cardinality lemma](../PrimeFactors/ProductAdvice.lean)

## Singular roots and short ranges of cofactors

Let $r_k(t)$ be the number of square roots of $t$ modulo $2^k$, with $r_0(t)=1$. For odd $a$, every positive $m$, and every $C\ge1$,

$$\sum_{c=1}^{C} r_k(a+m^2c^2)\le20C+32\sqrt{2^k}.$$

For an odd target there are at most four roots: for any odd root $y$ and another root $z$, one of $z-y,z+y$ has exactly one factor of two, so the other must be divisible by $2^{k-1}$ when $k\ge3$. The two smaller positive exponents are immediate. For an arbitrary nonzero residue of valuation $2u<k$, write its root as $2^u z$ and divide the congruence by $2^{2u}$. There are at most $4\cdot2^u$ roots before division. An odd valuation below $k$ gives zero roots. The zero residue has $2^{\lfloor k/2\rfloor}$ roots. Consequently

$$r_k(t)\le4\sum_{j=0}^{\lfloor k/2\rfloor} 2^j\,\mathbf1_{4^j\mid t}.$$

If $m$ is even, all the targets are odd and $4C$ suffices. Otherwise, for $j\ge1$ the condition $4^j\mid a+m^2c^2$ selects at most four classes of $c$ modulo $4^j$, since $m$ is invertible and $-a$ is odd. At most $4(C/4^j+1)$ integers in the range belong to these classes. Summing both geometric series gives the displayed bound, including the contribution from singular classes near the endpoints. Lean verifies the pointwise bound, counts the cofactor classes and sums the series to give $20C+32\cdot2^{\lfloor k/2\rfloor}$. [Formal mass and cell bounds](../PrimeFactors/DyadicMass.lean) · [Elementary square-root classification and computation modulo prime powers](https://www2.math.uu.se/~lakelind/kompendier/Talteori.pdf)

## Adding the cells and conditioning on 2048 bits

Since $Q\le X$ and $B\ge1$, the cofactor sum is at most $72\sqrt{XB}$ per modulus. One cell can therefore account for at most $72W\sqrt X T$ successful integer pairs. Every split on the next high or low bit halves $W$, even if different leaves request different bits. The sum of $W$ over the leaves is at most $X$. This gives at most $72X^{3/2}T$ successful pairs. Counting composite candidates in this upper bound costs a logarithmic factor and permits the full half-width of advice.

The explicit prime count in the prescribed-budget note gives at least $(0.22X/\log X)^2/2$ eligible unordered prime pairs. Dividing the two counts and using $\log X<710$ gives a success probability at most $[144\cdot710^2/0.22^2]T/\sqrt X<2^{30.5}T/\sqrt X$ for $T>0$. Substituting $T=2^{40}$ gives the headline inequality. For the analogous population at growing widths, the same argument gives $O(T(\log X)^2/\sqrt X)$. If the selector reads a fixed proportion fewer bits, sieving both factors removes the logarithmic loss and gives the optimal order. The result covers menus prescribed by bits read from the two ends. Interior probes at freely chosen indices, and decisions using unrestricted functions of $N$, require a different bound. [Sharp asymptotic theorem](sieved-product-advice.md) · [Explicit prime-count constants and source](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)

## What the best small tables actually select

The bounded experiment enumerates *all* exactly double-width products of two distinct primes of a given bit length. It computes the most successful table retrospectively, with two nominal test slots per input. This measures the strongest table for the population, including fitting it on the very same products. At this budget the complete options are two ordinary Fermat midpoints, one test per root at modulus 2, or one per root at an odd prime power. A modulus with two prime divisors has at least four roots of one modulo its square. The experiment factors the small half-gaps to score these options; this preprocessing uses the labeled population. [Exact optimizer](../experiments/product_advice.py) · [Independent small exhaustive check](../tests/test_product_advice.py)

| Factor bits | Eligible pairs | One fixed menu | High bits only | Split between ends | Low bits and the leading one |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 7 | 42 | 36 | 40 | 40 | 40 |
| 9 | 543 | 286 | 373 | 344 | 364 |
| 11 | 5,530 | 1,597 | 2,324 | 2,157 | 2,210 |
| 13 | 64,719 | 9,575 | 14,882 | 13,631 | 13,677 |

Each table uses one factor-width of product bits, counting the leading one. The middle column uses equally many high and low bits after the leading one. Preprocessing cost and population changes matter to interpreting these counts. Run `python3 experiments/product_advice.py 7 9 11 13` to reproduce them.
