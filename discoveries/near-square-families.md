# Near-square totients with unbounded squarefree part

There are infinitely many balanced prime pairs $p<q<2p$ for which the product alone recovers the factors in at most **49 discriminant tests**, even though the squarefree part of $\varphi(pq)$ exceeds any prescribed bound. Here the squarefree part $\operatorname{sf}(a)$ is the unique squarefree $d$ with $a=d y^2$. More precisely, one fixed $k\in\{1,\ldots,49\}$ occurs along a sequence with unbounded squarefree part, $q/p$ tending to a constant strictly between 1 and 2, and
$$\varphi(N)=(\lfloor\sqrt N\rfloor-1)^2-k^2.$$
For any fixed $L\ge1$, allowing these square errors alongside error zero in a search for $\varphi(N)=d y^2-e$ with $d\le L$ therefore strictly extends the inputs covered by exact bounded square classes. The infinitude argument is unconditional and uses a theorem on 50 admissible linear forms. [Exact square-class decoder](discriminant-strides.md) · [Kim, Lemma 2.1](https://www.csun.edu/~sungjin/SJK_Totient2-3%281%29.pdf#page=4)

## The product-only calculation

For $200\le j\le249$, set $P_j(t)=j^2t+2j+1$. Suppose $p=P_i(t)$ and $q=P_j(t)$ are prime, $i<j$ and $t\ge1$. Set $k=j-i$ and $Y=ijt+i+j$. Expanding gives
$$
(p-1)(q-1)=Y^2-k^2,\qquad
N=(Y+1)^2+k^2(t-1).
$$
The factor ratio is below two already at $t=1$ and for every larger $t$, since $P_j(t)\le250^2t<2\cdot200^2t<2P_i(t)$. Since $2ij>k^2$, the last term is smaller than $2Y+3$, so $s=\lfloor\sqrt N\rfloor=Y+1$. For each $1\le k\le49$ with $k^2\mid N-s^2$, try
$$S=N+1-(s-1)^2+k^2.$$
If $S^2-4N$ is a nonnegative square, use its root to reconstruct the two factors and verify their product. Only $N$ is supplied. For $N=20995182420991$, $s=4582050$ and $N-s^2=218491$. The surviving $k$ are 1, 7 and 49. The last gives $3680401\cdot5704591$. Here $i=200$, $j=249$, $t=92$ and $\operatorname{sf}(\varphi(N))=2\cdot5\cdot29\cdot79\cdot83\cdot3067=5831992510$.

A 92-bit example shows the filter working before the factors are known. For $N=2723154578512940020180564043$, $N-\lfloor\sqrt N\rfloor^2=1985348667707$. Through $k=43$ only 1 and 43 have squares dividing this residual. The second discriminant gives $42949673760401\cdot63403382146843$. The prime $130459634047$ divides the totient exactly once, so every exact square-class multiplier is at least that large. The certificate for the larger factor also proves this auxiliary prime is prime. With the index-gap cap set to 42, the same search leaves the full input unresolved. [Decimal benchmark and control](../benchmarks/square-offset.json) · [Lean identities, integer-root decoder and multiplier bound](../PrimeFactors/PredecessorCount.lean)

## Simultaneous primality and large squarefree part

Fix $L$. For each index $i$ choose a distinct prime $r_i$ larger than $L$, 249, and all $|i+2j(i-j)|$ for the 50 indices $i,j$. These integers are nonzero. When $j\le i$ they are positive, and when $j>i$ we have $2j(j-i)>i$. Require
$$it+2\equiv r_i\pmod {r_i^2}.$$
Then $r_i$ divides $P_i(t)-1=i(it+2)$ to exponent exactly one. For $j\ne i$, the residue of $i(P_j(t)-1)$ is $2j(i-j)\ne0\bmod r_i$. Every $P_j(t)$ is also a unit modulo $r_i$, since $iP_j(t)\equiv i+2j(i-j)\bmod r_i$. Thus if $P_i(t)$ and $P_j(t)$ are prime, their totient has both $r_i$ and $r_j$ in its squarefree part.

To handle the small primes, require $t$ even. At each odd prime $\ell\le50$ choose a quadratic nonresidue $\nu_\ell$ and impose $t\equiv1-\nu_\ell\bmod\ell$. The coefficient $t$ is nonzero, and the polynomial $t j^2+2j+1$ in the index $j$ has nonsquare discriminant $4\nu_\ell$. Thus all 50 forms are units at $\ell$. The Chinese remainder theorem combines these conditions and the private prime conditions into a single progression $t=t_0+Mu$ with $t_0>0$.

The resulting 50 forms in $u$ are admissible. At a prime dividing $M$ the preceding checks apply. At any other prime $\ell>50$, a form with $\ell\mid j$ is identically one, and each remaining form excludes just one residue of $u$. The 50 forms cannot cover all residues. Their leading coefficients are positive, and their pairwise determinants are nonzero because $(2j+1)/j^2$ is strictly decreasing and an affine substitution with slope $M>0$ preserves nonproportionality.

Kim's quantitative general-linear-forms theorem gives $\gg_L X/(\log X)^{50}$ positive parameters with at least two prime values and all values at most $X$, for sufficiently large $X$ depending on the fixed progression. Each specified pair of indices has strictly increasing product, so a product can be counted at most $\binom{50}{2}$ times. This yields the same order of lower bound for distinct products at fixed $L$. The implied constant depends on the progression for this $L$. [Kim, Lemma 2.1](https://www.csun.edu/~sungjin/SJK_Totient2-3%281%29.pdf#page=4)

As $L$ increases, the 1,225 possible index pairs stay fixed, and the squarefree parts are at least $r_i r_j>L$. At least one pair of indices must therefore have unbounded squarefree parts. Along such a sequence $t\to\infty$, $q/p\to(j/i)^2\in(1,2)$ and the error remains the single fixed square $(j-i)^2$. Pigeonholing gives existence of the recurring pair.

## Comparison with weighted Fermat

Ordinary Fermat search needs $\Theta(\sqrt N)$ midpoint increments along the recurring family, since $(p+q)/2-\sqrt N\sim(j-i)^2t/2$. The weighted Fermat method can also exploit the family. Indeed
$$j^2p-i^2q=(j-i)(2ij+i+j)$$
is constant at fixed $i,j$. Dividing its square by $j^2p+i^2q+2ij\sqrt N$ shows that $j^2p+i^2q=\lceil2ij\sqrt N\rceil$ for sufficiently large $t$. One weighted discriminant test then suffices for the correct weights, which can be included in a finite list independent of $N$. The separation proved here concerns bounded *exact totient square classes*. Establishing a speed advantage over weighted Fermat would require a different comparison. [Weighted Fermat windows](searching-the-balanced-interval.md) · [Lehman's factoring algorithm](https://doi.org/10.1090/S0025-5718-1974-0340163-2)
