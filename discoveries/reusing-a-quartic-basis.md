# Reusing a quartic basis in the next divisor interval

On the 49-bit product $502005281288939$, carrying five polynomials from one interval to the next reduced a complete scan from **176,999 to 71,471 LLL swaps**, and from 1.275 to 0.642 CPU seconds. Both searches recovered $17838631\times28141469$. On two generated 2,048-bit products, the four intervals following the first each took 9–18 swaps with reuse. Neither search found a factor in those intervals. This changes the cost per interval. The search still needs its interval locations. [Quartic interval and factor certificates](quartics-at-a-chosen-location.md) · [Comparison program](../experiments/quartic_basis_translation.py)

## Why a neighboring interval can use the old polynomials

For an odd product $n$, write a proposed divisor as $d=c+2x$, $|x|\le W$, and choose $t$ with $c+2t\equiv0\pmod n$. The quartic construction uses the lattice of polynomials $P$ of degree at most four with $n^2\mid P(t)$ and $n\mid P'(t)$. For the next odd progression, take $c'=c+2h$ and $t'=t-h$. Replacing each polynomial by $P(x+h)$ preserves both divisibilities at the new anchor. The inverse shift is $-h$, so a translated basis generates the entire new lattice. One can add a multiple of $n$ to the anchor since Taylor expansion preserves both divisibilities. Adjacent disjoint windows of $2W+1$ odd candidates use $h=2W+1$. [Translation identities in Lean](../PrimeFactors/QuarticBasisTranslation.lean)

At each center the program runs exact LLL with parameter $\delta=3/4$ on coefficients scaled by $(1,W,W^2,W^3,W^4)$. For every returned row it checks both divisibilities again. With $D=c-2W$, a row is short enough when $\sum_i|a_i|W^i<D^2$. At a genuine divisor every such polynomial must vanish at $x$. Some windows are certified empty by two parity checks. A short polynomial with odd constant term rules out even $x$, and one with odd coefficient sum rules out odd $x$. Five short basis rows always pass these joint checks, since the unscaled basis determinant is $\pm n^3$, which is odd. If a parity survives, the comparison isolates the integer roots of one short polynomial and verifies any proposed divisor by division. A window without a short row is reported as unresolved. [Divisibility and height proof](../PrimeFactors/QuarticDivisorWindow.lean) · [Exact reduction and root isolation](../experiments/norm_auxiliary.py)

## Bounding the number of swaps

Write $b_1,\ldots,b_5$ for the previous reduced **scaled** basis, $b_i^*$ for its Gram–Schmidt vectors, $g_i=\lVert b_i^*\rVert^2$, and $O_k=\prod_{i=1}^k g_i$. Size reduction gives $|\mu_{i+1,i}|\le1/2$. The Lovász condition then gives $g_{i+1}\ge g_i/2$. Let $m_k$ be the smallest squared $k$-dimensional volume spanned by $k$ independent vectors of this lattice. Then

$$m_k\ge 2^{-k(5-k)}O_k.$$

To see this, write any $k$ independent vectors in the old basis as the rows of an integer matrix $M$. Choose the lexicographically last ordered column set $J=(j_1,\ldots,j_k)$ with $\det M_J\ne0$. In the Gram–Schmidt basis, the coefficient of the exterior basis vector indexed by $J$ is still $\det M_J$. The change of coordinates is unit lower triangular, so a contributing minor indexed by $I\ne J$ would require $i_\ell\ge j_\ell$ for every $\ell$, contradicting the choice of $J$. Orthogonality bounds the squared volume below by $\prod_\ell g_{j_\ell}$. Now $g_{j_\ell}\ge 2^{-(j_\ell-\ell)}g_\ell$ and $\sum_\ell(j_\ell-\ell)\le k(5-k)$. The argument allows the old prefix volumes to exceed the corresponding minima. [LLL reduction and its potential, §1](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1982f/art.pdf)

On scaled row vectors translation has matrix $T_{ij}(r)=\binom ij r^{i-j}$ for $0\le j\le i\le4$, with zeros above the diagonal and $r=h/W$. Its inverse is $T(-r)$. Put $F_k(r)=\lVert\bigwedge^k T(r)\rVert_F^2$, the sum of the squares of all $k$-by-$k$ minors. Each minor is an integer binomial determinant times $r^{\sum i-\sum j}$, so $F_k$ is also the squared Frobenius norm for the inverse. With $u=r^2$, evaluating these small minors gives

$$\begin{aligned}
F_1=F_4 &=5+30u+46u^2+17u^3+u^4,\\
F_2=F_3 &=10+90u+227u^2+205u^3+80u^4+13u^5+u^6.
\end{aligned}$$

The Frobenius norm bounds the operator norm. Translation therefore multiplies each squared volume by at most $F_k$ and by at least $1/F_k$. In the new lattice the initial prefix volume divided by the intrinsic minimum, both squared, is at most $2^{k(5-k)}F_k^2$. For the LLL potential $P$, the product of the first four squared prefix volumes, the initial value is at most $R$ times the product of the four new minima, where

$$R=2^{20}(F_1 F_2)^4.$$

That product of minima bounds *every* final basis potential from below. Size reductions leave $P$ unchanged. At a swap only one prefix changes, by the factor $g_{i+1}/g_i+\mu_{i+1,i}^2<3/4$. Thus $s$ swaps require $(4/3)^s\le R$. For $W\ge1$, $r\le3$, so $F_1\le22955$, $F_2\le1992610$, and $3^{390}R<4^{390}$. This gives **at most 389 swaps**. For $W\ge65536$, use $r\le2+1/65536$. Exact rational substitution gives $3^{307}R<4^{307}$ and **at most 306 swaps**. These bounds apply after a reduced basis has been computed at the previous center, with the same $W$ and adjacent step. In the implemented loop, a successful Lovász test advances the row index and a swap lowers it by at most one. At most $4+2s$ iterations therefore occur, with at most four earlier rows considered per iteration. The initial reduction, Gram data, coefficient updates and the bit cost of the arithmetic remain to be paid.

The Lean file verifies the translation identities, the binomial minor coefficient tables, monotonicity, and the integer or rational inequalities taking a certified potential ratio to the swap caps. The comparison of the exterior minima and the swap formula for the LLL implementation are the paper steps above. The exterior calculation can be reproduced with `lake build PrimeFactors.QuarticBasisTranslation`. [Checked finite calculations and potential lemmas](../PrimeFactors/QuarticBasisTranslation.lean)

## Bounded comparisons

The small comparison covers every odd integer in the public equal-width smaller-factor range, using $W=291$ and 4,827 windows. The table reports all search arithmetic, including translation, rebuilding Gram data, the two divisibility checks on all five rows, the joint parity check, and the remaining root and divisor checks. CPU times on the arm64 Mac with Python 3.9.6 are medians of five runs with alternating order. The two full-size comparisons start at the public odd lower quartile at $W=2^{407}$, then process four adjacent windows. Their timings are medians of three runs with alternating order. They concern only those five windows. These timings use the standalone comparison script. The public benchmark also runs the translated search once per input and records the unvisited blocks. [Control products and first-window fixtures](../benchmarks/quartic-divisor-window.json)

| Input and portion timed | Reduction method | Swaps | CPU seconds |
| --- | --- | ---: | ---: |
| 49-bit control, complete | Fresh bases | 176,999 | 1.275 |
| Same coverage | Translated bases | 71,471 | 0.642 |
| Fresh 2,048-bit control, four updates after setup | Fresh bases | 2,403 | 2.286 |
| Same four updates | Translated bases | 57 | 0.057 |
| Crossed 2,048-bit control, four updates after setup | Fresh bases | 2,432 | 2.292 |
| Same four updates | Translated bases | 46 | 0.050 |

Including the shared first reduction, the five-window translated runs took 0.637 and 0.591 CPU seconds. On the 49-bit product, 4,760 windows had five short rows. The other 67 contained one actual factor window and 66 false positives for that rank test. The two parity checks cleared 55 of the 66. Isolating roots on the remaining 12 windows returned just one integer candidate, the successful divisor. On the full-size products all five rows were short in each sampled window. The measurements supply neither a global speedup factor nor a way to select the successful window from the product. The public fixtures record the remaining cofactor and the exact number of unvisited blocks for each capped run. [Complete 49-bit benchmark and certificate](https://marius-bughiu.github.io/prime-factors/#quartic-basis-translation-49) · [Fresh capped run](https://marius-bughiu.github.io/prime-factors/#quartic-basis-translation-fresh-2048) · [Crossed capped run](https://marius-bughiu.github.io/prime-factors/#quartic-basis-translation-crossed-2048)

```sh
python3 -m experiments.quartic_basis_translation --case small --rounds 5
python3 -m experiments.quartic_basis_translation --case controls --rounds 3
```

## What short equations say about the factor

All short rows must vanish at the same offset if a divisor lies in the window. Independent rows give separate linear constraints on the five quartic coefficients. More precisely, if $k>0$ independent polynomials of degree below $h$ vanish at $r$ distinct points in a field, then $k+r\le h$. The map sending a polynomial to its values at the $r$ points is onto for $r\le h$ by interpolation. Its kernel therefore has dimension $h-r$. Taking $h$ of the points rules out $r>h$ when there is a nonzero row. For quartics, five independent short rows therefore prove emptiness. For the actual integral rows there is also a two-check certificate: if one short row is odd at offset zero and another is odd at offset one, every integer offset fails. Lean checks both arguments. [Rank and parity proofs](../PrimeFactors/DivisorWindowRank.lean)

Can four short rows identify the winning interval? For $N=6901=67\times103$ and stride two, take all offsets between $-2$ and $2$. At center 69 the interval contains 67. At center 79 its possible factors are 75, 77, 79, 81 and 83. None divides 6901. In **both** windows the rational span of *every* short integral row satisfying the two divisibilities has dimension four. In the empty window one short polynomial is $((x-2)^2+3)^2$, which is positive everywhere. At the intermediate center 73 the exact dimension is five. The sequence four, five, four rules out using a monotone rank threshold to bisect even this one range. Both prime factors, both span dimensions and the window conditions are checked in Lean. [Counterexample](../PrimeFactors/QuarticRankCounterexample.lean)

Four rows can also give an exact candidate formula. Put their coefficients of $x,x^2,x^3,x^4$ in a matrix $A$, and put their negated constant coefficients in a column $b$. Write $\Delta=\det A$ and let $\Gamma$ be the determinant after replacing the first column by $b$. At a common integer root, $A(x,x^2,x^3,x^4)^T=b$, so $\Gamma=\Delta x$. If $\Delta\ne0$, a candidate factor in this window must equal $c+2\Gamma/\Delta$. Nonintegral quotients, out-of-range offsets and failed division tests reject it. Computing four suitable short rows at the right center is still required. [Cramer identity and recovery theorem](../PrimeFactors/DivisorWindowRank.lean)

On the complete 49-bit comparison, ten of the twelve windows left by the parity check had four short rows and a nonzero determinant. Nine gave a nonintegral quotient. At center 17,838,859 the two determinants were $\Delta=397559205769926792824245573379$ and $\Gamma=-114\Delta$. This gave offset $-114$ and divisor $17{,}838{,}859-228=17{,}838{,}631$. Directly checking all 583 offsets in each of the twelve windows confirmed the single common root. These calculations use the four rows from the translated search. The timed comparison used scalar root isolation and did not measure determinant speed.

## How far one equation can reach without another reduction

At a divisor $d=c+2x$, the same polynomial $P(x)$ is always a multiple of $d^2$. The original window used the sum of its absolute coefficient bounds to ensure $|P(x)|<d^2$. Beyond that window we can test the actual polynomial instead. Keep the consecutive integer offsets around zero for which **both** $(c+2x)^2-P(x)$ and $(c+2x)^2+P(x)$ are positive. Signed forward differences partition each quartic into monotone integer stretches, where binary search locates the endpoints. To verify each stretch, the certificate checks the signs of coefficients in the Bernstein basis on a few subintervals. The two immediately adjacent offsets fail the strict inequality. This proves maximality for that connected run and that chosen polynomial. Other polynomials can cover different locations. [Magnitude and endpoint proof](../PrimeFactors/QuarticIntervalExtension.lean) · [Exact sign search](../experiments/quartic_interval_extension.py)

At the two public quartiles the old polynomial covered **2.38×** and **10.48×** as many consecutive odd positions as its original coefficient bound. The calculation still paid for one initial lattice reduction. Extending it required 41,724 and 45,025 polynomial sign evaluations, respectively, over the default domain from 1 to $N$. Lean checked the final interval with two pieces on the fresh example and three on the crossed example. The same original modular witnesses (7 and 29) exclude every integer root throughout. Both products remain unresolved by these runs. [Fresh certificate and counts](https://marius-bughiu.github.io/prime-factors/#quartic-window-extension-fresh-2048) · [Crossed certificate and counts](https://marius-bughiu.github.io/prime-factors/#quartic-window-extension-crossed-2048)
