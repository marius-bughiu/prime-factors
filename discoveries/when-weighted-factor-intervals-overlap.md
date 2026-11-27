# What merging factor intervals can save

Projecting the weighted search onto possible smaller factors eliminated **one even integer out of 11,961,038 locations** across twelve independent products. Every odd candidate remained. This explains why sorting and merging the intervals added work to both trial division and a quotient-curve search on these inputs. There is a stronger restriction in the other direction. For the actual factors, **at most two primitive positive multipliers can succeed** in the entire rectangular search. [Measurements and factor certificates](../research/merging-weight-intervals.json) · [Lean proofs](../PrimeFactors/WeightWindowOverlap.lean)

## The interval attached to a weight pair

Take $N=pq$ for two distinct odd primes. We search $y^2=x^2+kN$ with $0<y\le B$, $0\le x\le H$, $B+H<N$ and $HB<N$. The prior cofactor theorem assigns relatively prime weights $a\le b$ to the hidden primes. Write $t=1$ when both weights are odd and $t=2$ when they have opposite parity. Then $k=t^2ab$. For the smaller candidate $P$, put $Q=N/P$, allowing $P$ to range over real numbers. The midpoint and signed difference are

$$Y=\frac{t(bP+aQ)}2,\qquad X=\frac{t(bP-aQ)}2.$$

The intervals $|X|\le H$ and $Y\le B$ must both hold. The larger weight must multiply the smaller candidate whenever $P>H$. In the reverse orientation, $t(bQ-aP)\ge t(b-a)P\ge2P$ for distinct weights. Equal relatively prime weights give only $(1,1)$. [Cofactor theorem](../PrimeFactors/MixedUnityCofactors.lean) · [Orientation proof](../PrimeFactors/WeightWindowOverlap.lean)

For integer $P$, the experiment solves the two quadratic inequalities $t|bP^2-aN|\le 2HP$ and $t(bP^2+aN)\le 2BP$ with exact integer square roots and endpoint rounding. It intersects each result with $\max(2^{w-1},\lceil N/(2^w-1)\rceil)\le P\le\lfloor\sqrt N\rfloor$, where $w$ is the common prime width. The search only uses $N$ and $w$. It still has to check divisibility at surviving candidates. [Implementation and endpoint oracle](../experiments/merging_weight_intervals.py) · [Tests](../tests/test_merging_weight_intervals.py)

## Why at most two windows can meet

Write $(A_i,C_i)=(t_i b_i,t_i a_i)$ for two windows. The two coordinates in each pair have matching parity. At any candidate $P$ their midpoint and difference satisfy the exact identity

$$X_1Y_2-X_2Y_1=\tfrac{N}{2}(A_1C_2-A_2C_1).$$

Distinct reduced ratios give a nonzero integer in parentheses. It is even, so the absolute determinant is at least $N$. If both signed differences are nonnegative, the two products on the left lie between $0$ and $HB$. The same bound on their difference holds when both differences are nonpositive. Hence at most one window from each side of the candidate ratio can cover $P$. For two windows with $t=2$, the determinant is a multiple of $2N$, while its absolute value is at most $2HB$, so they cannot overlap even on opposite sides. Merging visits to *any* fixed set of candidate locations therefore saves at most a factor of two. This is a multiplicity bound. It does not require that the locations are integer divisors. [Geometric separation and no-three-window proof](../PrimeFactors/WeightWindowOverlap.lean)

At the actual prime pair there are two possible assignments of the primes to $y-x$ and $y+x$. For two primitive successes with the same assignment, both $p$ and $q$ divide $x_1y_2-x_2y_1$. Its absolute value is at most $HB<N$, so it vanishes. The fractions $x_1/y_1$ and $x_2/y_2$ are in lowest terms, giving identical coordinates and the same $k$. Thus the set of positive primitive winning multipliers has size at most two. Four of the twelve products exhibited two windows at their true divisor, and the other eight exhibited one. For example, $2{,}496{,}395{,}833=44{,}249\times56{,}417$ lies in the windows for $(a,b,t)=(29,37,1)$ and $(11,14,2)$. [Formal primitive row count](../PrimeFactors/WeightWindowOverlap.lean) · [Per-product windows](../research/merging-weight-intervals.json)

## Why even a false divisor gets a window

A one-unit relaxation makes the geometric test accept **every** odd candidate $P$ coprime to $N$ with $H+1\le P\le\sqrt N$, where $H=\lfloor N/(B+1)\rfloor$. Set $Q=N/P$. The relaxed bounds are $|X|<H+1$ and $0<Y\le B+1$. Both $X$ and $Y$ may be rational. A candidate sharing a nontrivial gcd with $N$ already supplies a factor.

To see this, apply the Chinese remainder theorem to $P^2$ and $N$. Choose a root that is $+1$ modulo $P^2$ and $-1$ modulo $N$. The integer rectangle lemma gives coordinates $x',y'$ for this root modulo $P^2N$ with $0<y'\le P(B+1)$ and $|x'|<P(H+1)$. Now $P^2$ divides $y'-x'$ and $N$ divides $y'+x'$. The two resulting integer quotients have matching parity because $P$ and $N$ are odd. Their weighted midpoint at $(P,Q)$ is $y'/P$ and the absolute difference is $|x'|/P$. Positivity of the midpoint and $|x'|/P<P$ force both weights to be positive. Dividing out a common factor gives the two coprime parity families used by the search, while preserving both bounds. This construction uses the **candidate** $P$, and works even when $N/P$ is nonintegral. [Canonical relaxed coverage and exact counterexample](../PrimeFactors/RelaxedWeightCoverage.lean)

The one-unit distinction is necessary. At $N=38{,}957=163\times239$, with $B=1{,}145$ and $H=33$, the exact geometry excludes the prime candidate $P=167$. The relaxed window for weights $(1,1)$ admits it. On the two 2,048-bit controls the enlargement changed neither $\lfloor B^2/N\rfloor$ nor the rounded upper weight-ratio used by the generator. [Checked example](../PrimeFactors/RelaxedWeightCoverage.lean) · [Full-size parameters](../research/merging-weight-intervals.json)

## Complete searches and full-size costs

We took the first four products of each width in the existing independently drawn weight panel. Times below are single-run process CPU milliseconds, summed per width. The projected method includes generating, sorting and merging its ranges before trial division to the first factor. The last column uses the existing one-lane traversal testing square differences on weighted rows. All twelve recovered prime pairs were checked by Lean. [Prior independent draw](../research/rectangular-multiplier-products.json) · [Complete results and certificate hashes](../research/merging-weight-intervals.json)

| Bits per prime | Integer locations | Excluded by union | Projected trial, ms | Full interval trial, ms | Weighted rows, ms |
|---|---:|---:|---:|---:|---:|
| 16 | 42,680 | 1 | 1.64 | 0.72 | 1.86 |
| 20 | 755,761 | 0 | 16.43 | 12.35 | 3.17 |
| 24 | 11,162,597 | 0 | 103.35 | 70.84 | 8.90 |

On the first product of each width we also ran the repository's existing quotient-curve search with modulus 30 on the merged ranges and on the full interval, using the same precomputed cell width and residue classes. Both schedules used exactly 64, 448 and 2,576 cells respectively, and the same number of quadratic solves. The only excluded integer in the twelve-product panel was 57,792 for $N=3{,}515{,}645{,}813$. A prime-only divisor scan would therefore inspect exactly the same candidates before and after merging on every product in this panel. [Quotient-strip implementation](../experiments/secant_quotient_cells.py) · [Related weighted-ratio search](farey-weighted-sums.md)

For each 2,048-bit input we evaluated every weight pair with $k\le65{,}536$ and computed interval endpoints. All 2,529 nonempty windows on the fresh input were disjoint, as were all 5,699 on the crossed input. The window from $k=1$ alone contains more than $2^{681}$ odd candidate divisors on each input. The full prefix union contains about $2^{687.76}$ and $2^{688.67}$ integer positions, respectively. We counted those positions without visiting them. Neither prefix was used to claim a factor. [Public endpoint counts](../research/merging-weight-intervals.json)

Run `python3 -m experiments.merging_weight_intervals --output build/merging-weight-intervals.json` to reproduce the comparisons. The implementation reuses this repository's MIT-licensed weight generator, quotient-cell scanner and Lean certificate checker. [Experiment](../experiments/merging_weight_intervals.py) · [License](../LICENSE)
