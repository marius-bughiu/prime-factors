# Checking a short part of the factor curve with one line

On each of our two 2,048-bit examples, four groups of possible factor pairs previously left more than $2^{492}$ positions to check. Keeping the same groups, we can cover their entire search with **fewer than $2^{175}$ tests**. We choose short pieces of the curve so that one equation per sign is enough on each piece. We can count the pieces without visiting them. The count on each input still exceeds $2^{173}$ pieces. We visited three on each and found no factor. The four chosen groups may contain no winning position. [Original groups](lifting-a-signed-gap.md) · [Inputs and budgets](../benchmarks/offset-tangent-cover.json)

## How the product sets the length of a piece

Assume $N=pq$ with distinct, balanced odd primes. For a guessed pair of positive coprime coordinates $s,v$, write $k=sv$ and $P=4Nk^2$. The public trace runs in a progression $S=A+\delta i$ with positive step $\delta$. At the correct coordinates the height $w=|ps^2-qv^2|$ satisfies $w^2=S^2-P$. Earlier arithmetic gives a public affine residue for the signed gap modulo $M$. For each of its two signs the resulting possible heights have the form $w=r+\beta i+My$ for some integer $y$.

At the start of a piece compute $u=\lfloor\sqrt{A^2-P}\rfloor>0$ and $e=A^2-P-u^2$, so $0\le e\le 2u$. Put $x=\delta i$. The key integer identity is

$$
(uw-u^2-Ax)(uw+u^2+Ax)=u^2e-(P+e)x^2.
$$

The second factor is at least $2u^2$. Thus, throughout $0\le i\le W$, every true height obeys

$$
-\left\lfloor\frac{(P+e)(\delta W)^2}{2u^2}\right\rfloor
\le uw-u^2-A\delta i\le u.
$$

For the lower bound one can replace $e$ with $2u$. The implementation keeps the tighter value at the actual piece. Substituting the height residue puts $(i,y)$ between two parallel lines. Their unscaled vertical separation is at most $u+\lfloor (P+2u)(\delta W)^2/(2u^2)\rfloor$ at scale $uM$. [Tangent identity and bounds](../PrimeFactors/OffsetTangentCover.lean)

Both of the following integer conditions suffice to make the area of the resulting strip at most $1/4$ in the $(i,y)$ lattice.

$$
8W\le M,\qquad 4(P+2u)\delta^2 W^3\le M u^3.
$$

A continued fraction now gives a line containing **every** candidate for that sign. Intersecting it with $w^2=S^2-P$ costs at most one integer square root and produces at most two indices. A zero quadratic coefficient reduces the test to a linear equation or a nonzero constant. Every recovered pair must pass exact division and multiply to $N$. For a singleton piece one direct square test handles both signs. Lean proves the one-line statement for positive width, including the floor at the starting height. [One public line on the tangent strip](../PrimeFactors/OffsetTangentCover.lean) · [Intersection equations](lines-on-a-factor-arc.md)

## Counting the complete partition

Process index zero as a singleton. Split the rest of a progression of length $n$ into blocks $[1,2),[2,4),[4,8),\ldots$, clipped at $n$. For the block beginning at $I$, compute the floor height $u_I$ once. Choose the smaller of $\lfloor M/8\rfloor$ and the integer cube root of $\lfloor M u_I^3/[4(P+2u_I)\delta^2]\rfloor$ for $W$, and give each piece at most $W+1$ positions. The last piece may be shorter. As the height increases, $(P+2u)/u^3$ decreases, so the initial width meets the two inequalities everywhere in the block. The number of pieces follows by a single ceiling division. Counting uses one square root and one cube root per noninitial block. Executing a piece additionally needs its own bound and, for positive width, up to two continued fractions and two line tests. [Monotonicity proof](../PrimeFactors/OffsetTangentCover.lean) · [Count and bounded search](../experiments/offset_tangent_cover.py)

| Input | Coordinates | Blocks counted, including index zero | Pieces on the complete schedule for those coordinates | Upper bound on line or singleton tests |
| --- | ---: | ---: | ---: | ---: |
| $502005281288939$ | All 613 | 18,859 | 22,933 | 39,825 |
| Fresh 2,048-bit product | Four sampled | 12,174 | between $2^{173.187}$ and $2^{173.188}$ | below $2^{174.188}$ |
| Crossed 2,048-bit product | Four sampled | 16,248 | between $2^{173.470}$ and $2^{173.471}$ | below $2^{174.471}$ |

These are exact integer schedule counts in the fixtures, with rounded bounds for the two large rows in the table. The test ceiling counts one per singleton and two per other piece, including when no projected line exists. On the 49-bit input the complete subdivision needed 6,041 singleton checks and 7,513 line equations. It recovered $17{,}838{,}631\times28{,}141{,}469$. The earlier fixed-band search that chooses between lines and individual points used only 1,664 checks there. Across 1,265 products of two distinct same-width 5–9-bit primes the subdivision and the two fixed-band variants all recovered the full set of 1,344 independently reconstructed winning positions. [Benchmarks](../benchmarks/offset-tangent-cover.json) · [Fixed-band comparison](../benchmarks/offset-arc-lines.json)

A comparison with known work matters at this scale. Hiary gave a deterministic algorithm that uses continued fractions to test divisor intervals in $N^{1/3+o(1)}$ bit operations. The result here supplies an explicit integer curvature condition and a count for a search over weighted-factor coordinates. The sampled counts are specific to that search. The implementation reuses the project’s continued fractions and Euclidean floor sums. The new curvature inequalities and their Lean proofs were developed here. [Hiary's interval algorithm](https://arxiv.org/abs/1408.2608)
