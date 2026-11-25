# How many factor remainders can use the same quartic?

For each of the four recorded searches at 600 and 604 bits, the quartic computed for remainder 1 can serve **only that remainder**. In fact, no integer in any other class satisfies even the dyadic part of its congruence. This result uses the public products and recorded coefficients. It applies to reusing the same polynomial at the same modulus. A different polynomial, a weaker divisibility target or a relation known only for actual factors requires a separate argument. [Recorded searches](projected-quartic-levels.md) · [Lean proof](../PrimeFactors/QuarticLaneReuse.lean)

## A sharp limit for two entire classes

Let $R=2^e$, and let $F$ be an integer quartic with nonzero leading coefficient $c$. Suppose $8R^4$ divides $F(x)$ for all integers in the two distinct classes $u,v\pmod R$. Write $v-u=Hz$ with $H=2^t$, $z$ odd and $t<e$, and put $r=R/H$. Then **$4r^2$ divides $c$**. In particular, every pair of distinct classes requires $16\mid c$. The same result holds when the solver promises divisibility only for odd integers coprime to 30 in an odd lane. Each odd grid point can be replaced by a unit congruent to it modulo $8R^4$, since that modulus is coprime to 15. [Five-point divisibility and unit transfer](../PrimeFactors/QuarticLaneReuse.lean)

To see the power of two exactly, evaluate $P(t)=F(u+Ht)$ at $0,r,2r,z,z+r$. The cross differences between the two groups are odd. With $O=z(z+r)(z-r)(z-2r)$, Lagrange interpolation expresses $2r^2O$ times the leading coefficient of $P$ as an integer linear combination of these five evaluations. The multipliers in that order are

$$
(z-r)(z-2r),\quad -2(z+r)(z-2r),\quad z(z+r),\quad -2r(z+r),\quad 2r(z-2r).
$$

The leading coefficient of $P$ is $H^4c$. Canceling $2r^2H^4$ gives $4r^2\mid Oc$. The integer $O$ is odd, so $4r^2\mid c$. The bound is attained by

$$
4r^2(X-u)(X-u-R)(X-v)(X-v-R).
$$

On either class the two matching factors contribute $R^2 k(k-1)$ and the other two are multiples of $H$. The product is divisible by $8R^4$. For an odd product $N$, multiplying this example by $45N^2$ also supplies the odd part of $360R^4$ and makes it representable as $dN^2+bNX+fX^2+aX^3+cX^4$, without changing the power of two in its leading coefficient. This example establishes sharpness of the congruence constraint. The search must also control the real size of the trace.

## How to find all classes without another reduction

Let $h=v_2(c)$. Given one valid center $u$, every other center is congruent to $u$ modulo $2^{e-b}$, where $b=\max(0,\lfloor(h-2)/2\rfloor)$ is capped at $e-1$ for odd centers. Test just those $2^b$ possibilities. Five consecutive evaluations per candidate give an exact whole-lane test. If $K\ge2$ classes survive, choose a pair with the smallest separation valuation $t$. All $K$ classes lie in one residue modulo $2^t$, so $K\le r$ and $|c|\ge4K^2$. In the centered sum basis $c=v_3+v_4$. The projected spread therefore satisfies $S\ge4K^2\min(2s^2,2sB)$, where $s$ and $B$ are the public sum and factor radii. A shared polynomial allows one common unscaled level-image sieve, with any surviving integer roots still checked against the enlarged set of remainders. Lower-degree polynomials with $c=0$ need a separate bound. [Centered weights](centered-factor-sum.md) · [Finite-grid criterion and spread inequality](../PrimeFactors/QuarticLaneReuse.lean)

## Consequence for the cost of a complete sweep

On the fresh 2,048-bit input, allowing a genuine quartic to serve all its valid centers still leaves the existing lower bound of $2^{247}$ work units for an exhaustive sweep by genuine quartics. This statement uses the [projected sweep cost model](projected-sweep-budget.md). The radix is $R=2^e$ with $e\le600$, the modulus is $M=360R^4$, blocks contain at most $65{,}536$ level positions, and a complete query costs $W$, the larger of one and the number of blocks visited. The coverage count may credit both orders of the factors. It measures a complete sweep, irrespective of whether an earlier group would find a factor.

For $K=1$ certified center the existing proof gives $RW\ge2^{249}$. For $K\ge2$, let $w$ be the smallest of the four nonconstant weighted-coordinate bounds. Then $A=\min(2s^2,2sB)\ge w^2/2$, since both $2s$ and $B$ are at least $w$. The two-lane theorem gives $2S\ge4w^2K^2$. If $L$ is the integer level count, the interval has $L\ge\lfloor2S/M\rfloor$ and the scanner has $L\le65536W$. Thus $2S<M(65536+1)W$. Combining the two inequalities and using $W\ge1$ gives

$$
\frac{RW}{K}>\frac{2w}{R\sqrt{360\cdot65537}}>2^{400}.
$$

The final inequality uses the fresh product's checked $2w\ge360\cdot2^{1009}$, $R\le2^{600}$ and $\sqrt{360\cdot65537}<2^{13}$. A query with $K$ valid centers can cover at most $2K\cdot2^{600-e}$ fine remainders including factor order. Therefore $RW/K\ge2^{249}$ suffices for the same $2^{247}$ total lower bound. This corollary assumes every query has nonzero quartic leading coefficient and that the scanner visits its level blocks. Sharing work between unrelated polynomials or skipping those blocks requires a different cost analysis.

## Product-only checks

| Trace source | $e$ | $v_2(c)$ | Valid centers | Single-point roots outside that class |
|---|---:|---:|---:|---:|
| Crossed control | 600 | 0 | 1 | 0 |
| Fresh control | 600 | 0 | 1 | 0 |
| Crossed control | 604 | 3 | 1 | 0 |
| Fresh control | 604 | 2 | 1 | 0 |

The last column uses a stronger coefficient test. Expand $F(u+z)=\sum_{i=0}^4a_i z^i$ and set $C=2^{v_2(c)}$ and $T=R/2$. In all four rows, $2CT^{4-i}\mid a_i$ for $i<4$ and $2CT^4\mid8R^4$. If $z=2^t q$ with $q$ odd and $2^t\mid T$, division by $C2^{4t}$ leaves an odd fourth-degree term and even lower terms. Such a point cannot satisfy the required dyadic congruence. Lean proves this criterion and the script checks the actual coefficients. [Product-only replay](../experiments/quartic_lane_reuse.py)

We also recomputed a trace for every existing sign-and-swap group at $R=32$ and 64 for the eight frozen holdout products, supplying only their public $N$ values. At $R=32$, 8 of 35 traces covered multiple centers; at $R=64$, 8 of 67 did. Every extra center belonged to the original group. Of those 35 and 67 traces, 20 and 14 had degree below four, respectively. Exhaustive five-point checks over all odd centers included them. A concrete example from the separate $N=96{,}577$ control covers both 7 and 23 modulo 32, but $7\cdot23\equiv N\pmod{32}$ so swapping the factor order already covers both. Run `python3 -m experiments.quartic_lane_reuse` to replay the four large checks and the 102 holdout reductions. [Frozen inputs](../research/quartic-lane-holdout.json) · [Small example](../research/projected-quartic-levels.json)
