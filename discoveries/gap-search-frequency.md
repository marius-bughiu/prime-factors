# How often does a stride find the factor gap?

Choose two distinct primes uniformly without replacement from $[X,2X)$ and order them as $p<q$. Given only their product $N=pq$, a square-root search can exploit a divisor $m$ of the half-gap $D=(q-p)/2$. Trying all products of powers of $s$ fixed primes succeeds on a proportion

$$
  \Theta_S\!\left(\frac{(\log X)^s}{\sqrt X}\right)
$$

using $O_S((\log X)^s)$ midpoint square tests. Giving consecutive Fermat search the same predetermined number of midpoint tests yields a proportion $\Theta_S((\log X)^{s/2}/\sqrt X)$. Both proportions tend to zero. The statements below are unconditional paper deductions; Lean verifies the underlying midpoint search and its completeness for a given stride. McKee applied this squared-modulus idea in a rational version of Fermat search. [Lean search theorem](../PrimeFactors/GapStride.lean) · [Stride construction and implemented base-five search](smooth-factor-gaps.md) · [McKee, *Speeding Fermat’s factoring method*](https://doi.org/10.1090/S0025-5718-99-01133-3)

A matching optimization theorem bounds the coverage of *every* prescribed list under a nominal midpoint-test budget and constructs lists that attain the bound. [Optimality among prescribed searches](stride-budget.md)

## What one test per root covers

Let $r=\lceil\sqrt N\rceil$, $H=(p+q)/2$, and $Y=\lfloor\sqrt X\rfloor$. For each root of $h^2=N\bmod m^2$, test the first $h\ge r$ in its class. A successful split must be proper. The genuine midpoint is tested exactly when $m\mid D$ and $H-r<m^2$. Indeed, $H^2-N=D^2$, so $m^2\mid H^2-N$ is equivalent to $m\mid D$. The identity

$$
   D^2=(H-\sqrt N)(H+\sqrt N),\qquad 2X\le H+\sqrt N<4X
$$

shows that $m\mid D$ and $D/m\le Y$ suffice. Conversely, if the test finds the pair, then $H-r\le m^2-1$ and $r<\sqrt N+1$ give $D/m<2\sqrt X$. These two implications bound the *actual* coverage, including hits outside the sufficient condition. [Checked per-class search](../PrimeFactors/GapStride.lean)

## A fixed set of small primes

Fix a finite set $S$ of $s$ primes. Remove all prime powers supported on $S$ from $D$, leaving the positive integer $c$. The event $c\le Y$ means that some $S$-smooth $m\mid D$ has $D/m\le Y$. Its probability is $\Theta_S(Y(\log X)^s/X)$. The same estimate holds if $Y$ is multiplied by any fixed positive constant.

**Upper bound.** There are $O_S((\log X)^s)$ possible $m\le X$ by counting exponent tuples. For each fixed $p$ and $m$, count primes $q$ in $(p,p+2mY]$ with $q\equiv p\bmod 2m$. The short-interval Brun–Titchmarsh bound is $2h/(\varphi(d)\log(h/d))$ for an interval of length $h>d$ and a reduced class modulo $d$. Here $h/d=Y$ and $2m/\varphi(2m)$ is bounded in terms of $S$. Thus each $p$ has $O_S(Y/\log X)$ possible partners for that $m$. There are $P\asymp X/\log X$ choices of $p$ by the prime number theorem. Divide the union bound by $\binom P2$. [Montgomery and Vaughan, *The large sieve*, Theorem 2](https://doi.org/10.1112/S0025579300004708)

**Lower bound.** Fix a sufficiently large integer $L$ and take moduli $m=\prod_{\ell\in S}\ell^{Lj_\ell}\le X^{1/4}$ with $j_\ell\ge0$. For $s>0$, allowing $0\le j_\ell\le\lfloor\log X/(4sL\log\ell)\rfloor$ already gives $\gg_S(\log X)^s$ choices. For $S$ empty take $m=1$. For each $m$, partition the primes by successive half-open bins of length $2mY$ and by reduced residue class modulo $2m$. There are $J\ll X\varphi(2m)/(2mY)$ boxes. Cauchy–Schwarz bounds the number of unordered pairs in common boxes below by $(P^2/J-P)/2$, hence by

$$
   C\,\frac{2m}{\varphi(2m)}\frac{XY}{\log^2 X}
$$

for an absolute $C>0$ and large $X$. The diagonal term is negligible since $Y/\log X\to\infty$. Every pair counted has $m\mid D$ and $D/m\le Y$.

Discard a pair for this $m$ if $m\ell^L\mid D$ for any $\ell\in S$. Apply Brun–Titchmarsh to $(p,p+2mY]$ with modulus $2m\ell^L$. Since $\log(Y/\ell^L)\asymp\log X$ for fixed $S,L$, the discarded count is at most

$$
   C'\,\frac{2m}{\varphi(2m)}\frac{XY}{\log^2 X}
   \sum_{\ell\in S}\frac{1}{\ell^L(1-1/\ell)}.
$$

The constants can be chosen independently of $L$ once $X$ is sufficiently large for those fixed primes and exponents. Choose $L$ so the sum times $C'$ is smaller than $C/2$. For every remaining pair, $j_\ell=\lfloor v_\ell(D)/L\rfloor$ for all $\ell\in S$, so only one selected modulus counts that pair. Sum the lower bound and divide by $\binom P2$.

The input-only search tries all $S$-smooth $m\le\lfloor\sqrt N\rfloor$. This includes every smooth divisor of $D\le X/2$. On a hit $c\le D/m<2\sqrt X$, so the upper estimate also applies to its success probability. For sufficiently large $X$ all its bases are coprime to $N$. At most two roots occur at an odd prime power and at most four at a power of two. CRT bounds the total per modulus by $2^{s+1}$. Reuse the roots along a tree of exponent tuples, assigning each node one parent by deleting one prime factor. Extending $m$ to $m\ell$ takes two base-$\ell$ digit lifts, each costing $O_S(1)$ trials per root. The worst-case total is $O_S((\log X)^s)$ arithmetic operations on $O(\log X)$-bit integers, counting square tests as individual operations. Inputs with missing roots can terminate branches early.

## A band of auxiliary primes

Fix $0<\beta<1/2$ and use the primes $m\equiv3\bmod4$ in $[X^\beta,2X^\beta]$. Their number is $K\asymp_\beta X^\beta/\log X$ by the prime number theorem in the fixed progression modulo four. With one test per root the success probability is **$\Theta_\beta(K/\sqrt X)$**.

For each $m$, the same box argument gives $\gg XY/\log^2 X$ pairs with $m\mid D$ and $D/m\le Y$. The only size restriction used there is $mY\ll X$, which holds throughout this band. Another distinct band prime $m'$ can divide $D$ for at most $O_\beta(XY/(m'\log^2 X))$ of those pairs. Indeed the combined congruence has modulus $2mm'$, while the interval for $q$ still has length $2mY$ and $\log(Y/m')\asymp_\beta\log X$. Since $\sum_{m'}1/m'=O_\beta(1/\log X)$ on this single band, deleting overlaps preserves the lower order for each $m$. The survivors can be summed disjointly. For the upper bound on every actual hit, use $m\mid D$ and $D/m<2\sqrt X$ in the single-modulus Brun–Titchmarsh estimate and sum over the band. [Short-interval sieve bound](https://doi.org/10.1112/S0025579300004708)

At the endpoint $\beta=1/2$, distinct primes in $[\sqrt X,2\sqrt X]$ cannot both divide $D\le X/2$. Every pair with $m\mid D$ passes the one-test budget. Cauchy–Schwarz over residue classes alone gives $\gg P^2/m$ pairs per prime, and Brun–Titchmarsh in the full interval gives $O(P^2/m)$. The total proportion is $\Theta(1/\log X)$.

**Computing the band from the product.** For a dyadic population $X=2^b$, $X\le\sqrt N<2X$, so $X$ is the largest power of two at most $\lfloor\sqrt N\rfloor$. For arbitrary $X$ the population scale can be public. It can also be dispensed with by trying the band from that power of two and from half of it. Every pair then tests the common band based on $2^{\lfloor\log_2 X\rfloor}$. For $\beta<1/2$ all tested primes lie within constant multiples of $X^\beta$, so the proofs give the same orders. At $\beta=1/2$, take the common subband $[\sqrt{2X_0},2\sqrt{X_0}]$ for $X_0=2^{\lfloor\log_2 X\rfloor}$; it lies above $\sqrt X$ and contains $\asymp\sqrt X/\log X$ eligible primes. The upper bound still follows from the single-modulus sieve.

An ordinary prime sieve constructs the list in $K(\log X)^{O(1)}$ bit operations. For a listed prime, test $u=N^{(m+1)/4}\bmod m$ for $u^2=N\bmod m$. On a match the two roots are nonzero; each has a unique lift $u+mt\bmod m^2$ with $t=((N-u^2)/m)(2u)^{-1}\bmod m$. This gives at most $2K$ midpoint tests and $K(\log X)^{O(1)}$ total bit operations. It uses direct root extraction and lifting at large primes. The repository's small-base benchmark implements successive powers of five. [McKee’s squared-modulus factoring method](https://doi.org/10.1090/S0025-5718-99-01133-3) · [Base-five benchmark implementation](../experiments/gap_stride.py)

## Positive coverage from a wider range

Fix $1/2<\gamma<1$ and try every prime $m\equiv3\bmod4$ in $[\sqrt X,X^\gamma]$. The success probability tends to **$\tfrac12\log(2\gamma)$**. Every $m\mid D$ in this range is caught in one test per root, and no two such primes divide the same half-gap. Cauchy–Schwarz over the $m-1$ nonzero classes gives $\gg P^2/m$ unordered pairs per modulus, uniformly since $m=o(P)$. Brun–Titchmarsh on the full interval gives $O_\gamma(P^2/m)$. Summing and using the prime number theorem in the progression $3\bmod4$ already gives a positive proportion.

For the precise limit, let $P_a$ count the sampled interval's primes in class $a\bmod m$, and put $V_m=\sum_{a\ne0}(P_a-P/(m-1))^2$. The number of **ordered distinct** pairs whose half-gap is divisible by $m$ is $P^2/(m-1)+V_m-P$. Character orthogonality writes $V_m$ as $(m-1)^{-1}\sum_{\chi\ne\chi_0}|\sum_{X\le p<2X}\chi(p)|^2$. Every nonprincipal character of prime modulus is primitive. Applying the multiplicative large sieve to the indicator of the primes in the interval therefore bounds $\sum_{m\in[Q,2Q]}V_m$ for the selected primes by $O((X/Q+Q)P)$. Summing dyadic pieces gives $O(X^\gamma P\log X)=o(P^2)$, and all diagonal terms together are also $o(P^2)$. Disjointness allows us to divide the sum by $P(P-1)$. The result is $\sum_m1/(m-1)+o(1)=\tfrac12\log(2\gamma)+o(1)$ by partial summation. Changing either endpoint by a bounded factor contributes $O_\gamma(1/\log X)$ to coverage, by the single-modulus upper bound, so the public dyadic-scale implementation has the same limit. [Montgomery and Vaughan, large sieve for primitive characters](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf)

The list and all per-prime tests cost $X^{\gamma+o(1)}$ bit operations, or $N^{\gamma/2+o(1)}$. Since $\gamma/2>1/4$, the guaranteed $N^{1/5+o(1)}$ general factorization algorithm is asymptotically cheaper and covers every target. [Harvey and Hittmeir](https://arxiv.org/abs/2105.11105)

## Equal budgets and the general factorization bound

For $T\ge1$ consecutive Fermat midpoints starting at $r$, success is $H-r<T$. The identity for $D^2$ places this event between $D\le\sqrt{XT}$ and $D<2\sqrt{XT}$. If $U$ is a fixed multiple of $\sqrt{XT}$ and $X^{1/2}\ll U\ll X^{1-\epsilon}$ for fixed $\epsilon>0$, the proportion with $D\le U$ is $\Theta(U/X)$. The lower bound follows by putting all primes into intervals of length $2U$ and applying the same box count. Brun–Titchmarsh with modulus one gives the upper bound.

For the fixed set take $T\asymp_S(\log X)^s$. For the prime band take $T\asymp K$, giving Fermat coverage $\Theta(\sqrt{K/X})$. Even granting Fermat $K(\log X)^{O(1)}$ midpoint tests to account for the band’s bit-operation overhead, its coverage is $X^{\beta/2-1/2+o(1)}$. The band’s coverage is $X^{\beta-1/2+o(1)}$ for $0<\beta<1/2$. For the entire range through $X^\gamma$, granting Fermat $X^{\gamma+o(1)}$ tests yields $X^{(\gamma-1)/2+o(1)}$ coverage, which tends to zero. These comparisons use predetermined budgets across the same prime-pair population. The dyadic-band method leaves most inputs unresolved even at its endpoint. General deterministic algorithms factor *every* input in $N^{1/5+o(1)}$ bit operations; the results here describe the coverage of an elementary bounded search. [Harvey and Hittmeir](https://arxiv.org/abs/2105.11105) · [Stănică’s preprint on the secondary factor](https://arxiv.org/abs/2611.06580)

### Testing every auxiliary prime

Including the primes $m\equiv1\pmod4$ doubles the limiting fraction in the wide band to **$\log(2\gamma)$**. The prime events are still disjoint, and the variance proof now sums over all primes. For example, at $\gamma=3/4$ this is about 40.55% of pairs, asymptotically. The bit cost is $N^{3/8+o(1)}$ in that example. This is a paper result about a population as $X\to\infty$. [Multiplicative large sieve, Theorem 19.16](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf#page=186)

At each new prime, Tonelli–Shanks takes polynomially many bit operations once a quadratic nonresidue is available. Dirichlet GRH gives a deterministic polynomial-in-$\log m$ bound for finding one **at each prime**. There is also an unconditional deterministic bound for the **whole band**. Erdős proved that the least quadratic nonresidue has a finite mean over the odd primes. Scanning integers in order at each prime therefore takes $O(\pi(X^\gamma))$ Legendre tests in total, since the positive costs over the band are bounded by those over all primes up to its upper endpoint. Lifting to $m^2$ then uses one linear congruence per root, as in the preceding algorithm. [Martin and Pollack on the mean and the GRH bound](https://arxiv.org/pdf/1112.1175#page=1) · [Tonelli–Shanks algorithm](https://flintlib.org/doc/algorithms/number-theory/sqrt-mod-p.html) · [Verified Dirichlet result and sources](../docs/research.md)

## Finite coverage and measured work

At $X=2^{20}$ we sampled 20,000 distinct prime pairs uniformly without replacement, using seed 20261124. We tested primes $m\equiv3\pmod4$ in $[101,202]$ with one midpoint per root. The bound was 22 midpoint tests per product. Each run stopped when it found a factor. The experiment checked each answer against the exact condition $m\mid D$ and $H-r<m^2$. [Experiment](../experiments/gap_coverage.py) · [Lean equivalence](../PrimeFactors/GapStride.lean)

| Search | Pairs factored | Other work on the sample |
| --- | ---: | --- |
| Auxiliary prime band | 1,076 | 213,798 midpoint tests, 214,303 modular powers and 107,281 inverse/lift steps |
| Consecutive Fermat, at most 22 tests | 646 | 594 successes were missed by the band |
| Consecutive Fermat, at most 88 tests | 1,238 | 1,687,049 midpoint tests |

Across three runs of the last comparison, median search times were 0.264 seconds for the prime band and 0.208 seconds for the longer consecutive search. The equal-square-test advantage at this size did not translate to a time advantage. Earlier in the range, on all 104,196 distinct pairs for $X=4000$ and auxiliary primes in $[15,30]$, the band found 10,016 and the four-test consecutive scan found 21,158. Reproduce the sampled comparison with `python3 experiments/gap_coverage.py 1048576 --band 101 --sample 20000 --fermat-multiple 4`.
