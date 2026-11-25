# How many consecutive weighted sums can a common table omit?

For every prime $\ell>733$ and all weights with $\ell\nmid 2abN$, there is a cyclic run of **five consecutive residues** that the weighted sum $ap+bq$ cannot occupy when $pq=N$. The start of the run depends only on $abN\bmod\ell$. Translating each search row by its own start puts these five exclusions at the same five table positions. The cutoff is sharp: at $\ell=733$ the regular discriminant parameter $4abN=719\bmod733$ admits no five-site run. A longer guarantee grows with $\ell$. Extracting a factor still requires searching the surviving sums.

For a small example, let $N=77$, $a=b=1$, and $\ell=17$. A possible sum $s$ needs $s^2-4N\equiv s^2-2$ to be a square modulo 17. At $s=3,4,5$ the three discriminants are $7,14,6$, all nonsquares. A table indexed by $s-3$ can skip indices $0,1,2$ modulo 17. The actual sum $7+11=18$ has index $15$ modulo 17 and survives.

## The local equation

Work in $\mathbf F_\ell$ for an odd prime $\ell\nmid abN$. A possible weighted sum has the form $s=au+bN/u$ with $u\ne0$. Conversely, $au^2-su+bN=0$ has a root exactly when $s^2-c$ is zero or a square, where $c=4abN$. Its constant term is nonzero, so every root is a unit. Write $\chi$ for the quadratic character with $\chi(0)=0$. A residue is absent precisely when $\chi(s^2-c)=-1$. This reduction also covers a search in a progression $s=s_0+di$ at every selected prime where $d$ is a unit. After division by $d^2$, the discriminant in the index is $(i+s_0/d)^2-c/d^2$. [Exact one-prime image sizes](../PrimeFactors/ResidueCount.lean)

Let $J\subset\mathbf F_\ell$ have $k$ distinct positions, $1\le k<\ell$. Write $R_c(J)$ for the number of $x$ at which *every* $x+j$, $j\in J$, is absent. Then

$$
R_c(J)\ \ge\ \frac{\ell+1}{2^k}
 -\bigl(k-2+2^{1-k}\bigr)\sqrt\ell-k .
$$

For nonsquare $c$ the final $-k$ can be dropped. This holds for an arbitrary fixed template, including consecutive positions and translated arithmetic progressions. Each $c$ may use a different $x$.

## Why overlaps between the quadratics do not invalidate the count

Take a nonempty $I\subseteq J$ and choose $\rho^2=c$ in an algebraic closure. If $I$ contained $j-2\rho$ for every $j\in I$, it would contain the $\ell$ distinct points $j-2n\rho$, $n\in\mathbf F_\ell$, since $2\rho\ne0$. Thus some $j\in I$ has $j-2\rho\notin I$. At $X=\rho-j$, exactly one factor in

$$
P_I(X)=\prod_{i\in I}((X+i)^2-c)
$$

vanishes. Its derivative there is $2\rho$. Therefore $P_I$ has a simple root even when some of its other roots coincide. This excludes every scalar multiple of a square. The strict inequality $k<\ell$ matters for square $c$: taking $I=\mathbf F_\ell$ then gives each field element twice as a root. [Lean proof of the escaping shift and simple root](../PrimeFactors/TranslatedImageRuns.lean)

Every root has multiplicity at most two, since its value determines at most two possible indices $i$. For $h=|I|$, let $r$ be the number of double roots over the algebraic closure. Write $P_I=F G^2$ with $F,G$ monic and squarefree, having disjoint roots. The simple and double roots form Frobenius-stable sets, so both polynomials have coefficients in $\mathbf F_\ell$. The monic polynomial $F$ has even degree $e=2h-2r\ge2$. The even-degree Weil bound gives $|1+\sum_x\chi(F(x))|\le(e-2)\sqrt\ell$. Removing the square factor changes the sum at at most $r$ field points, by at most one per point. Consequently

$$
\left|1+\sum_x\chi(P_I(x))\right|
 \le (2h-2r-2)\sqrt\ell+r \le (2h-2)\sqrt\ell .
$$

The analytic inequality is a published theorem over finite fields. Gyarmati and Müllner also use irreducible translated quadratics in their proof of Theorem 1.4. Sárközy and Stewart describe earlier Weil-bound counts for patterns of ordinary Legendre symbols. The argument here applies this line of work to the two local square classes of the weighted discriminant. [Katz, introduction, p. 6](https://web.math.princeton.edu/~nmk/mellin357.pdf#page=6) · [Gyarmati and Müllner](https://doi.org/10.2478/udt-2023-0006) · [Sárközy and Stewart, pp. 1–2](https://cacr.uwaterloo.ca/techreports/2004/cacr2004-07.pdf)

Expand $\sum_x\prod_{j\in J}(1-\chi((x+j)^2-c))$ by subsets. The empty subset contributes $\ell$. Each nonempty subset contributes $(-1)^h(-1+E_I)$ with $|E_I|\le(2h-2)\sqrt\ell$. The constant terms sum to $\ell+1$. Each index belongs to $2^{k-1}$ subsets. Therefore the combined error has absolute value at most $((k-2)2^k+2)\sqrt\ell$. A genuine run contributes $2^k$. A position where any sign is positive contributes zero. At the at most $2k$ positions with a zero sign the contribution is at most $2^{k-1}$ apiece. Subtracting their combined upper bound and dividing by $2^k$ gives the displayed lower bound. Nonsquare $c$ has no zero signs. Lean checks the subset expansion and the three pointwise weight statements, as well as the simple-root argument. The Weil estimate and its use in the aggregate inequality are paper steps. [Formalized statements](../PrimeFactors/TranslatedImageRuns.lean)

There is also a separate Lean theorem for the underlying curve estimate with a larger constant. Math Inc.’s `riemann_hypothesis_hec` bounds the absolute deviation of the affine point count from $\ell$ by $5m\sqrt\ell$ for a geometrically nonsquare polynomial of degree $m\ge3$ with $\ell>6m$. Here $m=2h$. For $h=1$, the point count is exactly $\ell-1$ by the bijection $(X+j-y)(X+j+y)=c$ with pairs of product $c$. Thus for $\ell>12k$, applying that theorem to $h\ge2$ in the same expansion yields $R_c(J)\ge\ell/2^k-5k\sqrt\ell-k$ on paper. Our independent Lean lemmas `mapped_not_square` and `curve_count` establish its geometric hypothesis and the exact conversion to the character sum. The external theorem has been kept as a citation. The November 2026 RH release concerns the Riemann zeta function and Dirichlet $L$-functions. The curve bounds here hold over finite fields. [Math Inc., theorem statement](https://github.com/math-inc/RiemannHypothesisCurves/blob/main/RiemannHypothesisCurves/RiemannHypothesisHEC.lean#L564-L573) · [Local Lean lemmas](../PrimeFactors/TranslatedImageRuns.lean) · [The November release](https://github.com/leanprover-community/riemann-hypothesis#theorem-statements)

## Explicit cutoffs

Set $B=(k-2)2^k+2$, $L=\ell+1-k2^k$. The lower bound is positive if $L>0$ and $L^2>B^2\ell$. For fixed $k$, once this holds it continues to hold at larger primes, since $z^2-Bz+1-k2^k$ has exactly one positive root and $z=\sqrt\ell$. For $\ell\ge2^{16}$ put $t=\log_2\ell$ and $k=\lfloor t/2-\log_2t\rfloor$. Then $2^k\le\sqrt\ell/t$ and $1\le k\le t/2$, so the main term is at least $t\sqrt\ell$ and the total loss is at most $k\sqrt\ell+k<t\sqrt\ell$.

For the consecutive template $J=\{0,\ldots,k-1\}$, direct enumeration below the analytic cutoff gives the following sharp thresholds. All odd primes above the last failure work for **every** $c\ne0$.

| Run length | First prime guaranteed by the inequality | Last failing prime | All failing $c$ at that prime |
|---:|---:|---:|---|
| 1 | 3 | none | none |
| 2 | 17 | 11 | 9 |
| 3 | 149 | 41 | 21, 36 |
| 4 | 1,279 | 313 | 236 |
| 5 | 9,923 | 733 | 719 |

Run the bounded check with `python3 -m experiments.translated_image_runs`. Its initial bit set contains precisely those $c$ for which $-c$ is a nonsquare. A rotation by $s^2$ gives all $c$ for which $s^2-c$ is a nonsquare. Intersecting $k$ rotations tests one cyclic start for all $c$, and the union over starts determines which $c$ work. An independent test constructs the actual image $u+c/(4u)$ for every nonzero $c$ at every odd prime through 53 and compares it with those masks. [Finite enumeration](../experiments/translated_image_runs.py) · [Direct-image comparison and cutoff regression](../tests/test_translated_image_runs.py)

## Cost of using the exclusions

For consecutive sites, one can mark the squares once and scan two cyclic copies of the $\ell$ signs in $O(\ell)$ word operations per coefficient $c$. Keeping one start per $c$ for all regular rows costs $O(\ell^2)$ preprocessing operations and $O(\ell)$ words at that prime. For $t=\log_2\ell\ge16$ and the choice of $k$ above, there is also a faster randomized construction. Since $k2^k/\sqrt\ell\le1/2$ and $\sqrt\ell\ge256$, the loss $k(\sqrt\ell+1)$ is at most $257\ell/(512\cdot2^k)$. Thus $R_c(J)>\ell/(3\cdot2^k)$. A uniform trial shift works after at most $3\cdot2^k$ proposals on average for each $c$. Testing each proposal uses at most $k$ lookups in the marked squares. Filling all coefficients costs $O(\ell k2^k)$ expected word operations. Each accepted shift is checked directly.

With regular rows at several primes, the Chinese remainder theorem combines their individual translations. A shared baby table then retains exactly $\prod_{\ell}(\ell-k_\ell)$ residues per full period $M=\prod_\ell\ell$. Applying and reversing each row translation and handling the ends of the exponent interval also costs work. If exactly one weight vanishes at a prime, the corresponding image is every nonzero residue. A single translation can then omit only one position. The shared-table construction handles these singular rows using two rotations and includes the extra rows in its schedule count. The measured cutoffs concern regular rows. Their effect on total search cost depends on the resulting baby and giant tables. [Two-rotation construction and finite counts](weighted-residue-tables.md) · [Weighted windows and collision costs](farey-weighted-sums.md)
