# Finding points on an ellipse with auxiliary curves

Given positive integers $T$ and $d$, we can find every positive integer solution of $x^2+dy^2=T$ using $O(T^{1/4}\operatorname{poly}(\log T))$ bit operations. The algorithm uses only these two integers. It constructs a second polynomial on each short arc, then finds the integer roots of one univariate polynomial. At fixed auxiliary degree two the exponent is $3/10$, improving on the earlier straight-line scan's $1/3$. The quarter-power bound requires increasing the degree. Even $T^{1/4}$ is about $2^{512}$ at 2,048 bits. This theorem concerns the work of locating ellipse points. Recovering a factor requires two suitable points, possibly on different ellipses from a public list. [How the ellipse equations are chosen](searching-norm-directions.md) · [Lean proofs](../PrimeFactors/NormAuxiliary.lean)

The construction uses the determinant method of Bombieri and Pila, the idea of lattice searches near real curves developed by Elkies, and the LLL short-vector and polynomial-factorization theorems. We give the construction to make explicit how a search can compute its auxiliary polynomial before knowing any of its integer zeros. Harvey and Hittmeir's general deterministic integer factorization bound already has a smaller exponent. [Bombieri and Pila](https://people.maths.ox.ac.uk/pila/Ovals.pdf) · [Elkies](https://arxiv.org/abs/math/0005139) · [Lenstra, Lenstra and Lovász](https://ir.cwi.nl/pub/9304) · [Harvey and Hittmeir](https://arxiv.org/abs/2105.11105)

## A polynomial parametrization after clearing one denominator

If $d>T$ there are no solutions with positive $y$. Otherwise set $U=\sqrt T$ and $V=\sqrt{T/d}$, so both are at least one. The whole nonnegative quadrant of the ellipse has the parametrization
$$
x=U\frac{1-z^2}{1+z^2},\qquad y=V\frac{2z}{1+z^2},\qquad 0\le z\le1.
$$
Indeed, normalize the coordinates to $a=x/U,b=y/V$. They satisfy $a^2+b^2=1$, and $z=b/(1+a)$ gives the displayed formulas. Split $[0,1]$ into $J$ cells. In cell $i$, use $z=(i+u)/J$ with $0\le u\le1$.

Fix degree $D\ge1$. Take the $r=2D+1$ monomials $1,x,\ldots,x^D,y,xy,\ldots,x^{D-1}y$. Their degrees sum to $S=D(D+1)$. Write $M=r(r-1)/2=Dr$. After multiplying by $(1+z^2)^D$, each monomial becomes one positive amplitude $a_i$ times an integer polynomial from one of the following two lists.
$$
E_j=(1-z^2)^j(1+z^2)^{D-j},\quad 0\le j\le D,\qquad
O_j=2z(1-z^2)^j(1+z^2)^{D-j-1},\quad 0\le j<D.
$$
The amplitudes are $U^j$ in the first list and $U^jV$ in the second. Their product is $T^{S/2}d^{-D/2}$. These polynomials all have degree at most $2D$. Their coefficients describe the entire function on a cell with no series truncation.

Let $C$ be their coefficient matrix, with basis functions as rows and monomials in $z$ as columns. Reorder the columns by parity. In the even block, a unit triangular change of basis replaces $(1-w)^j(1+w)^{D-j}$ by $(2w)^j(1+w)^{D-j}$, where $w=z^2$. The binomial expansion of $((1+w)-(1-w))^j$ gives this change up to a diagonal sign. Its diagonal leading terms in ascending powers of $w$ are $2^j$. The odd block is the same construction in degree $D-1$, with an additional factor of two per row. Hence $|\det C|=2^S$. The affine substitution $z=i/J+u/J$ on degrees zero through $2D$ has triangular matrix of determinant $J^{-M}$. [Lean determinant identities](../PrimeFactors/NormAuxiliary.lean)

## Computing the auxiliary curve from the inputs

Compute each rounded amplitude $\tilde a_i=2^{-h}\lfloor 2^h a_i\rfloor$ separately, where $h=D+2D\lceil\log_2(2J)\rceil$. Their values come from integer square roots of rational squares after scaling. For example, the numerator for $U^jV$ is $\operatorname{isqrt}(\lfloor 2^{2h}T^{j+1}/d\rfloor)$. Each $\tilde a_i\ge1$ and $0\le a_i-\tilde a_i<2^{-h}$.

Form the square matrix of coefficients in $u$ of $\tilde a_iE_j((i_0+u)/J)$ and $\tilde a_iO_j((i_0+u)/J)$ for cell $i_0$. Multiplication by the common denominator $2^hJ^{2D}$ gives an integer matrix. Apply LLL with parameter $3/4$ to its rows and divide the first reduced row by the common denominator. Write the resulting polynomial as $H(u)=\sum v_j u^j$. Keep the nonzero integer combination $c$ of the original rows used by LLL. Their matrix is invertible, so $c$ can also be recovered by exact linear algebra.

With $\eta=\sum |v_j|$, the LLL bound, Cauchy–Schwarz and the determinant calculation give
$$
\eta\le\sqrt r\,2^{(r-1)/4}
  \left(\frac{2^S T^{S/2}}{d^{D/2}J^M}\right)^{1/r}.
$$
The uniform control of the rounding error requires a bound on $c$. Replacing $u$ by $Jz-i_0$ in $H$ gives a polynomial in $z$ with coefficient absolute sum at most $\eta(2J)^{2D}$, by the binomial theorem. Conversely each monomial $z^{2k}$ is a combination of the $E_j$ with coefficient absolute sum at most one. Explicitly, put $P=1+z^2$, $Q=1-z^2$ and expand $2^{-D}(P-Q)^k(P+Q)^{D-k}$. For $z^{2k+1}$ apply the same argument in degree $D-1$ and multiply by $(2z)/2$. This gives an absolute sum at most $1/2$ in the odd basis. The coefficients in this basis are precisely $c_i\tilde a_i$, hence $\sum |c_i|\le\eta(2J)^{2D}$.

Each basis function has magnitude at most $2^D$ for $0\le z\le1$. Restoring the original amplitudes therefore changes the value by at most $\eta(2J)^{2D}2^D2^{-h}\le\eta$. On its cell the rounded polynomial already has magnitude at most $\eta$. Choose $J$ large enough that the displayed LLL bound gives $\eta\le1/4$. The true scaled value is then at most $1/2$ in absolute value. For an integer point this value is the integer auxiliary evaluation $F(x,y)$ times $(1+z^2)^D\ge1$. This forces $F(x,y)=0$ at every integer point in the cell. The pointwise certificate $\eta+2^{D-h}\sum |c_i|<1$ also works whenever the actual LLL output satisfies it. [Lean small-integer criterion](../PrimeFactors/NormAuxiliary.lean)

## Extracting the points and counting the work

The recovered polynomial is $F(x,y)=P(x)+yQ(x)$, where $\deg P\le D$, $\deg Q\le D-1$ and at least one of the two polynomials is nonzero. Every common solution satisfies
$$
R(x)=dP(x)^2+(x^2-T)Q(x)^2=0.
$$
This polynomial has degree at most $2D$. If it were identically zero, both $P$ and $Q$ would vanish at every sufficiently large positive integer, since both coefficients of the squares are then positive. Thus $R$ is nonzero. Find its integer roots by factoring over the rationals and retaining its integer linear roots. For each candidate, check $T-x^2=dy^2$ by integer division and a square test, check the sign and $F(x,y)=0$, and keep the points in the requested cell. Membership uses integer comparisons since $x/U=(1-z^2)/(1+z^2)$ decreases on $[0,1]$. A half-open endpoint convention avoids duplicates. This procedure includes roots where $P(x)=Q(x)=0$. [Lean nonvanishing and root proofs](../PrimeFactors/NormAuxiliary.lean) · [Polynomial factorization algorithm](https://ir.cwi.nl/pub/9304)

The degree-two implementation isolates integer roots directly using the signs of the Bernstein coefficients on an integer interval $[l,l+w]$. When all coefficients have the same weak sign, the polynomial has that strict sign in the interior and its endpoints can be checked directly. Otherwise bisect the integer interval. This also has a polynomial worst-case bound. For a polynomial of degree $s$ with complex roots $\alpha_j$, if $|l-\alpha_j|>2sw$ for every root, then the sum of the absolute nonconstant coefficients of
$$
R(l+wu)/R(l)=\prod_{j=1}^{s}\left(1+\frac{wu}{l-\alpha_j}\right)
$$
is at most $(1+1/(2s))^s-1<1$. Conversion to Bernstein form weights each power coefficient of order $j$ by $\binom{m}{j}/\binom{s}{j}\le1$ in the coefficient at index $m$. Every Bernstein coefficient therefore has the sign of $R(l)$. Each bisected interval must have a root within distance $2sw$ of its left endpoint. At any depth of balanced integer bisection, the possible interval cardinalities differ by at most one. Each root can consequently account for $O(s)$ left endpoints at that depth, even for a nonreal root. The search visits $O(1+s^2\log(2+U))$ nodes for an initial interval of span $U$, including pruned siblings. All sign tests are integer computations. [Degree-two implementation](../experiments/norm_auxiliary.py)

Solving the bound on $\eta$ gives a sufficient cell count
$$
J\ \ge\ (4\sqrt r)^{1/D} 2^{1/2+(D+1)/(2D+1)}
             T^{(D+1)/(4D+2)}d^{-1/(2r)}.
$$
For degree two, $J=\lceil 8T^{3/10}d^{-1/10}\rceil$ suffices. With $D=\max(2,\lceil\log_2 T\rceil)$, $J=\lceil 8T^{1/4}\rceil$ suffices. Indeed $16(2D+1)\le9^D$ for $D\ge2$, so the first constant is at most three. The excess of the exponent of $T$ over $1/4$ is $1/(8D+4)$, costing a factor at most $2^{1/8}$. Also $(D+1)/(2D+1)\le3/5$.

Matrix dimension is $O(D)$. Common denominators, coefficients, and numerators have $O(D(\log(T+1)+\log(J+1))+h+D)$ bits by the binomial theorem. The bound on $c$ gives the same polynomial bit bound for the elimination polynomial. Computing all matrix entries, rational lattice reduction, tracking the combination, univariate factorization and checking the candidates have cost polynomial in the degree and bit lengths. Thus the variable-degree search takes $O(T^{1/4}\operatorname{poly}(\log T))$ bit operations. This is an upper bound from the construction. At degree two the lattice dimension is five. At the displayed variable degree for 2,048-bit $T$ it is about four thousand. The two bounds describe very different per-cell costs.

The parametrization, determinant, precision, nonvanishing and complexity calculations above are unconditional. Lean checks the algebraic lemmas identified in the links. The general LLL, norm and bit-complexity arguments here are on paper.

## Complete ellipse measurements

All four runs below searched the entire positive quadrant of $x^2+2y^2=1{,}900{,}014{,}700{,}027$. Each received the ellipse equation and returned exactly $(265493,956433)$ and $(657187,856773)$. The two representations give the factors $1{,}000{,}003$ and $1{,}900{,}009$. The line scan was the fastest on this input. The residue method visited the fewest blocks, with one five-dimensional lattice reduction per block. [Line scan](../experiments/norm_directions.py) · [Residue classes](../experiments/norm_residue_curves.py) · [Real sectors](../experiments/norm_auxiliary.py)

| Complete search | Blocks | LLL calls | Size reductions | Row swaps | Lines or auxiliary equations tested | Root-isolation intervals | Seconds |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Lines | 31,385 | 0 | 0 | 0 | 13,484 | 0 | 0.38 |
| Residue classes, degree two | 3,281 | 3,281 | 305,033 | 189,933 | 3,281 | 56,267 | 1.79 |
| Real sectors, basis reused | 36,026 | 35,909 | 580,825 | 301,419 | 1,511 | 6,779 | 6.63 |
| Real sectors, fresh basis | 36,026 | 35,909 | 2,127,101 | 1,353,894 | 1,494 | 6,724 | 16.99 |

For the sector runs, 117 blocks contained no integer $x$. To reuse a basis after advancing by $h$ sectors, replace $u$ with $u+h$ in each previously reduced quartic. This gives the same integer combinations of the translated input rows and supplies a starting basis for the next LLL call. The residue run also took 19,686 Hensel-lifting steps. The line run took 99,095 Euclidean steps and 13,364 discriminant square roots. Times are one local observation per method with CPython 3.9.6 on an arm64 Mac running macOS 27.0.1. They include search and point recovery. Certificate replay is timed separately in the benchmark report.

The public factor search stops once it has enough points. On this 41-bit input the degree-two residue search reached the second point after 3,094 classes. On $3599$ the residue and sector searches both split the product using representations from two different multiples. On the crossed 2,048-bit control the two-class residue budget examined two auxiliary equations, found zero representations and left the entire input unresolved. [Inputs and expected work](../benchmarks/norm-curves.json)
