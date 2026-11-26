# Certifying a block of missed divisors

On the independently generated 2,048-bit product, Lean checked that the first **64** integers in the feasible range for the smaller prime are all coprime to the product. On the smaller input 100,160,063 it checked the same fact for the **1,600** integers from 100 through 1,699. In both cases the inputs were the product and the chosen endpoints. These exclusions leave the full product to be factored. The larger example's feasible range contains more than $2^{1020}$ integers. [Construction of the 2,048-bit input](certified-fresh-control.md) · [Feasible interval](a-shorter-pascal-row-for-equal-width-primes.md)

## What Lean checks

Arrange the candidates as a grid of sums $b_j+a_i$. For consecutive integers, take offsets $a_i=i$ for $0\le i<d$ and block starts $b_j=L+dj$ for $0\le j<g$. Over the integers modulo the product $N$, form

$$
A(X)=\prod_i(X+a_i),\qquad B(X)=\prod_j(X-b_j).
$$

The certificate supplies polynomials $U,V$ for which $UA+VB=1$. Evaluate the identity at any block start $b_j$. The second term vanishes, so $A(b_j)$ has inverse $U(b_j)$. Every factor of $A(b_j)$ is then coprime to $N$. The same identity proves the claim for all $dg$ entries. Conversely, when every entry is coprime to $N$, such an identity exists even if some nodes repeat or their differences share a factor with $N$. For at least one node, one can supply just the $g$ coefficients of $U$ and check its product with $A$ has remainder one on division by $B$. The executable checker uses both $U$ and $V$, at most $g+d$ coefficients for nonempty grids. [Equivalence and degree bound](../PrimeFactors/FactorialBlockExclusion.lean) · [Coefficient and interval checker](../PrimeFactors/BlockExclusionCheck.lean)

## How the certificate is found

Start with $B=1$, $U=0$, and $V=1$. To add a block start $b$, set $c=V(b)/A(b)$ modulo $N$, then replace the three polynomials by

$$
B'=B(X-b),\qquad U'=U+cB,\qquad V'=\frac{V-cA}{X-b}.
$$

The numerator of the last expression vanishes at $b$, so the polynomial division is exact. Substitution gives $U'A+V'B'=1$. The implementation inverts all $A(b_j)$ together with one modular inversion. If their product shares a factor with $N$, individual gcds can locate a candidate and sometimes yield a proper divisor. The proof checks the extension step over any commutative ring. [Construction and verification](../experiments/block_exclusion_certificate.py) · [Lean proof](../PrimeFactors/FactorialBlockExclusion.lean)

There is also a direct check using one gcd of the product of all grid entries with $N$. Its input can be just $N$ and the endpoints. The polynomial construction takes $O(dg+g^2)$ coefficient operations after building $A$. Its certificate can be checked by multiplying polynomials built from the two short lists. The measurements cover the stated intervals only, and neither check identifies a promising place to search next.

For a direct comparison we computed $P_0=1$, $P_{k+1}=P_k(L+k)\bmod N$ inside Lean and checked $\gcd(P_{dg},N)=1$. Both checkers proved the same statement about every integer between the same endpoints. Median wall times over three runs, rotating the order and including Lean startup and imports, were **1.80 seconds direct versus 1.92 seconds polynomial** for the 64 positions and **1.84 versus 2.36 seconds** for the 1,600 positions. Both proof libraries were precompiled. Neither timing includes generation. The direct proofs also took fewer bytes to store in each example. [Public inputs, bounds and expected outcomes](../benchmarks/block-exclusion.json)
