# When a determinant gives the other factor

In the complete search of **502,005,281,288,939**, four equations supplied a number $D$ with a striking property. Dividing $D$ by the input gave **791,942,277,477,961**, the exact square of **28,141,469**. Dividing the input by that prime gave **17,838,631**. Lean verifies the determinant, the square root, both primes and their product. [Numerical proof](../PrimeFactors/QuarticMinorExample.lean)

**If $N=dq$ and four suitable equations vanish at the position of $d$, their determinant satisfies $|D|=Nq^2$.** This works without knowing either factor in advance. The four rows must belong to one full integer basis of the specified polynomial lattice. Arbitrarily scaling an equation can change the determinant. Our methods construct bases from the product and a chosen interval. They do not yet tell us which interval or basis will have the required four rows. [General Lean theorem](../PrimeFactors/QuarticDeterminantFactor.lean) · [How the intervals are chosen](quartics-at-a-chosen-location.md)

## Why the cofactor appears

Choose a public center $c$, a stride $s$ coprime to $N$, and an anchor $t$ with $N\mid c+st$. At a candidate offset $x$ the corresponding number is $d=c+sx$. Use five ordinary polynomials of degree at most four,

$$N^2,\quad N(X-t),\quad (X-t)^2,\quad X(X-t)^2,\quad X^2(X-t)^2.$$

Their coefficient matrix has determinant $N^3$. Integer row operations which have integer inverses preserve its absolute determinant and preserve the set of integer linear combinations of the rows. The five values at $x$ therefore have the same greatest common divisor before and after reduction. In the displayed basis this gcd is exactly $g^2$, where $g=\gcd(N,x-t)$. Indeed the first three values generate the same multiples as $g^2$ by squaring a Bézout identity for $N$ and $x-t$. The final two are already multiples of $(x-t)^2$. [Proof of the evaluation gcd](../PrimeFactors/QuarticDeterminantFactor.lean)

Suppose four rows of a reduced basis vanish at $x$. The value of the fifth must then have absolute value $g^2$. Replace the constant column of the coefficient matrix by the column of all five evaluations. This adds multiples of the four other columns to the constant column and preserves the determinant. Expanding along the replacement column gives

$$|D|g^2=N^3,$$

where $D$ is the determinant of the four vanishing rows with their constant coefficients removed. At a true divisor $d=c+sx$, the anchor and the coprimality of $s$ imply $\gcd(N,x-t)=\gcd(N,d)=d$. Dividing the formula by $d^2$ gives $|D|=Nq^2$. The formula holds for composite divisors and repeated prime factors as well. The earlier Cramer formula uses two determinants to recover the offset $x$; this identity uses one to recover $q$ directly. [Determinant proof](../PrimeFactors/QuarticDeterminantFactor.lean) · [Cramer formula](../PrimeFactors/DivisorWindowRank.lean)

## Which tests actually found a factor?

The search can try omitting each of the five basis rows. Even without a known root, the resulting determinants are multiples of $N$. Their signed quotients, up to an overall sign, are the five coefficients that express the constant polynomial $N^2$ in the current basis. Initially that list is $(1,0,0,0,0)$. Subtracting $m$ times row $j$ from row $i$ adds $m$ times coefficient $i$ to coefficient $j$. Swapping two rows swaps their coefficients. Translating all five polynomials to the next center preserves this representation, since translation fixes a constant. New information comes from the subsequent row reductions. A nontrivial gcd of a coefficient with $N$ immediately splits the input. A window with five unsuccessful gcds remains unresolved by this test, even when all scheduled windows have been visited. The equality with the normalized minor follows by replacing one matrix row by this linear combination and expanding the determinant. [Coefficient and minor proof](../PrimeFactors/QuarticMinorTracking.lean) · [Reproducible search](../experiments/quartic_minor_gcd.py)

| Product and portion tested | Windows | Coefficient gcds | Proper gcds |
| --- | ---: | ---: | ---: |
| 49-bit comparison, complete range | 4,827 | 24,135 | 1 |
| Fresh 2,048-bit comparison, five windows | 5 | 25 | 0 |
| Crossed 2,048-bit comparison, five windows | 5 | 25 | 0 |

On the 49-bit input the only hit was at zero-based window 910, centered at 17,838,859. The four rows that vanish at offset $-114$ gave $|D|=397559205769926792824245573379$. The factors used to check the benchmark were withheld from the search. On each full-size run the entire input remains as the unresolved cofactor. The only hit was in the same window that gave a factor through ordinary polynomial root isolation. Independently recomputing all 24,185 determinants across the three runs matched every tracked coefficient in absolute value. [49-bit run and factor certificate](https://marius-bughiu.github.io/prime-factors/#quartic-minor-gcd-49) · [Fresh run](https://marius-bughiu.github.io/prime-factors/#quartic-minor-gcd-fresh-2048) · [Crossed run](https://marius-bughiu.github.io/prime-factors/#quartic-minor-gcd-crossed-2048)

## What a square coefficient can mean

Four rows can also vanish at a rational offset $u/v$, with $u,v$ coprime and $v\ne0$. Multiply all evaluations by $v^4$ to make them integers. Their gcd becomes $g^2$ for $g=\gcd(N,u-tv)$. The absolute coefficient belonging to the sole nonvanishing row is then $(|N|v^2/g)^2$. A square can therefore arise even when the common root has a denominator. When $N$ is a product of distinct primes, the gcd of that coefficient with $N$ is $N/g$, since $v$ is coprime to $g$. We verify a split by dividing it into the input. [Homogeneous evaluation and square law](../PrimeFactors/QuarticHomogeneousImage.lean)

The same identity extends to higher powers. Write the basis in powers of $Y=X-t$, with row $i$ given by $N^{\max(m-i,0)}Y^i$, for $0\le i\le k$ and $m\le k$. Its determinant has magnitude $N^{m+\binom m2}$. When $k$ rows of a full integer basis vanish at the same divisor offset, the remaining $k$-by-$k$ minor has magnitude $N^{\binom m2}q^m$. The proof raises Bézout’s identity to power $m$ and uses the same determinant expansion. Requiring more vanishing rows is an additional condition at higher degree. [Arbitrary-degree Lean theorem](../PrimeFactors/PowerJetContent.lean)

The construction uses the classical lattice method for small polynomial roots modulo an unknown divisor. The exact identities here concern the values and minors of a complete integer basis. They require no hypothesis on zeta zeros or on the distribution of primes. The unfinished step for a general 2,048-bit product is to locate four useful rows substantially more cheaply than surveying the possible windows. [May, Theorem 7](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38) · [What the pinned Riemann repository supplies](../docs/research.md)
