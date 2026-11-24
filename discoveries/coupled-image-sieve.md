# Can coupled translations shrink a quadratic-image sieve?

**The exact minimum for any finite block of odd primes is the product of the one-prime minima.** Each required sign pattern specifies a Cartesian product of translated quadratic images, one in each coordinate. The translation at a prime may depend on every sign in the block. If all sign patterns must be retained, this freedom gives exactly the same smallest baby table as choosing an optimal pair of translates independently at each prime. The statement holds for every block size and every choice of distinct odd primes. [Finite compression proof in Lean](../PrimeFactors/CoupledImages.lean)

## Images of the actual baby index

In Stănică’s preprint, the baby index at a usable auxiliary prime $\ell$ is the image of a nondegenerate quadratic polynomial. Completing the square shows that an arbitrary translation gives one of two shapes. They are $c+Q_\ell^+$ or $c+Q_\ell^-$, where $Q_\ell^+$ contains zero and the nonzero squares, and $Q_\ell^-$ contains zero and the nonsquares. Both have $(\ell+1)/2$ elements. The least size of the union of one translate of each is
$$
 u_\ell=\frac{3\ell+\chi_\ell(-1)}4.
$$
Indeed, the complements are translates of the nonzero nonsquares and nonzero squares. The largest intersection of these complements has $(\ell-\chi_\ell(-1))/4$ elements, and the paper exhibits an attaining translation. The factorization algorithm uses a universal baby set and a giant-dependent translation. Its reported bit bound is $N^{1/5}\exp[-(\log(4/3)/50+o(1))\log N/\log\log N]$. [Stănică, Propositions 3.5–3.6 and Theorem 3.13](https://arxiv.org/html/2611.06580v1#S3)

For a squarefree auxiliary block $M=\prod_i\ell_i$, the Chinese remainder theorem identifies the baby indices with tuples. Write $P\subseteq\{+,-\}^t$ for the required leading-coefficient sign patterns. For each $\sigma\in P$ one may choose *all* centers $c_{\sigma,i}$ separately. The retained set must contain
$$
 U=\bigcup_{\sigma\in P}\prod_i(c_{\sigma,i}+Q_{\ell_i}^{\sigma_i}).
$$
The centers denote the final translates after completing the square. This model gives each sign pattern the full freedom of an arbitrary translate modulo $M$.

## Exact finite minimum

Fix one coordinate $i$ and choose an optimal pair of local translates $C_i^+,C_i^-$ with union size $u_{\ell_i}$. Keep all other coordinates fixed at a point $y$. The active rows are exactly those whose other coordinates contain $y$, so changing the $i$th translates does not change the active rows. The current section in coordinate $i$ has the following lower bounds.

| Signs of active rows at $i$ | Smallest possible section |
| --- | ---: |
| None | $0$ |
| Only one sign | $(\ell_i+1)/2$ |
| Both signs | $u_{\ell_i}$ |

For both signs, one active row of each sign already forces at least $u_{\ell_i}$ elements. Replace the $i$th translate of every row by $C_i^{\sigma_i}$. This one replacement attains the appropriate lower bound in every section simultaneously. Summing over $y$ shows that the new union is no larger. Repeating this in each coordinate proves, for any $P$, that a smallest union is
$$
 U_{\min}(P)=\bigcup_{\sigma\in P}\prod_i C_i^{\sigma_i}.
$$
With all $2^t$ sign patterns present the union is $\prod_i(C_i^+\cup C_i^-)$. Its exact cardinality and density are therefore
$$
 \min |U|=\prod_i u_{\ell_i},\qquad
 \frac{\min |U|}{M}=\prod_i\left(\frac34+\frac{\chi_{\ell_i}(-1)}{4\ell_i}\right).
$$
The Lean theorems **coupledImage_compress_coordinate**, **coupledImage_optimal**, and **coupledImage_full_product** prove the one-coordinate comparison, its iteration for arbitrary rows, and the full product formula as a lower bound attained by the displayed Cartesian construction. They apply to any two local families with the specified single-set and pair-union minima. The prime-specific values $u_\ell$ here use Stănică’s local calculation. [Lean proofs](../PrimeFactors/CoupledImages.lean) · [Local optimality formula](https://arxiv.org/html/2611.06580v1#S3)

If fewer sign patterns are required, the union can be smaller. For example, retaining only $(+,+)$ and $(-,-)$ leaves density tending to $7/16$ as both primes grow. Each of the two boxes has limiting density $1/4$ and their intersection has limiting density $1/16$. To use this in factorization one would have to prove that the omitted signs cannot occur or account for handling them elsewhere. The all-pattern result rules out improving the published bound by coupling translations alone.

## A strict penalty for a coupled pair

For two primes $p,q$, the independent construction retains density tending to $9/16$. Suppose all four patterns are required and at $p$ one sign uses *different final centers* for the two signs at $q$. The least possible limiting density under that extra condition is **$19/32$**. The following calculation also shows that such a coupling is strictly suboptimal at every $p\ge13$, regardless of the size of the other odd prime.

First replace the $q$-coordinate sets by the optimal fixed pair. This can only decrease the union. Their overlap has size $v_q=q+1-u_q\ge q/4$. At each point of this overlap all four rows are active. If two opposite signs at $p$ have the same center, their union is the entire field. Otherwise the four rows contain at least three distinct centers, because one sign is split and the other sign needs a center of its own.

At three distinct centers $c_1,c_2,c_3$, the uncovered fraction for three arbitrary signs is at most
$$
 \frac18+\frac1{4\sqrt p}+\frac3{8p}.
$$
To see this, majorize the indicator of being uncovered by $\prod_{j=1}^3(1+\epsilon_j\chi_p(x-c_j))/8$, taking $\epsilon_j$ as the sign opposite to the retained one. At a center the uncovered indicator is zero. In the expansion the linear character sums vanish, the three distinct-root quadratic sums equal $-1$, and the absolute value of the cubic character sum is at most $2\sqrt p$ by Weil. [Cochrane–Pinner on the pure multiplicative character bound](https://www.math.ksu.edu/~cochrane/research/stepmix.pdf#page=3)

At the other active positions of the $q$-coordinate, at least one row of each $p$-sign is active, costing $u_p$. Together these facts give
$$
 \frac{|U|}{pq}\ \ge\
 \frac{u_pu_q}{pq}
 +\frac{v_q}{q}\left(\frac78-\frac1{4\sqrt p}-\frac3{8p}-\frac{u_p}{p}\right).
$$
The parenthesis is at least $1/8-1/(4\sqrt p)-5/(8p)>0$ for $p\ge13$. As both primes grow, $v_q/q\to1/4$. The limiting density is thus at least $9/16+1/32=19/32$.

This penalty is sharp. At $q$ keep the optimal pair. At $p$ split the positive rows across two distinct centers and use a third common center for both negative rows. Where exactly one $q$-sign is active, a positive and negative translate at distinct centers cover $3/4+O(1/p)$ of the $p$-coordinate. In the overlap all three translates cover $7/8+O(1/\sqrt p)$ by the same character expansion, allowing at most three exceptional roots when counting either direction. These two regions occupy limiting fractions $1/2$ and $1/4$ at $q$, giving $(1/2)(3/4)+(1/4)(7/8)=19/32$. The strict penalty is a character-sum deduction on paper. The exact product minimum above has a separate finite proof in Lean.
