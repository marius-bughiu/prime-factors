# How much can a different integer-valued equation save?

For the fresh 2,048-bit input, a complete sweep of the possible smaller factor still needs **more than $2^{570}$ seven-row windows** when every window uses the project's depth-three determinant bound and treats every odd divisor coprime to 105 as eligible. For the crossed input the corresponding lower bound is **more than $2^{571}$ windows**. This holds for any choice of the seven degree-ordered integer-valued polynomials, any positions of the windows, and any valid lower divisor floors up to the square root. Only one always-eligible residue class is needed to prove it. [Lean proof and public input bounds](../PrimeFactors/IntegerLaneWindowWork.lean)

| Input | Residues sieved | Lower bound on total coefficient slots at variable degree and depth | Lower bound on seven-row windows at depth three |
|---|---|---:|---:|
| Fresh | Units modulo 3 | $>2^{505}$ | $>2^{575}$ |
| Crossed | Units modulo 3 | $>2^{506}$ | $>2^{576}$ |
| Fresh | Units modulo 105 | $>2^{500}$ | $>2^{570}$ |
| Crossed | Units modulo 105 | $>2^{501}$ | $>2^{571}$ |

A coefficient slot is one entry in a dense row of degree $k$ with $k+1$ entries. The variable-degree proof already bounds the smaller charge $\sum k$. It counts the whole geometric sweep, including overlaps, when every eligible position must lie in a window. A factor can be found before that sweep finishes. A new way of choosing a winning window, a separate proof excluding a subset of positions, or an equation that passes its actual height check outside the sufficient determinant bound can change the amount of work. [Earlier bounds specific to ordinary binomials](counting-binomial-coefficients.md) · [Observed wider windows](sifting-a-divisor-window.md)

## The finite-difference test for arbitrary polynomials

Let $P$ have rational coefficients and exact degree $i$, with leading coefficient $a_i\ne0$. On an arithmetic progression starting at $a$ with positive step $h$, its $i$th forward difference is $i!h^ia_i$. If the first $i+1$ samples are integers, the difference is a nonzero integer, so its absolute value is at least one. Now sample on the same progression at every $b$th position. The top difference scales by $b^i$. Its expression in those $i+1$ samples has signed binomial coefficients with absolute sum $2^i$. Thus a column with height bound $W_i$ on those samples must satisfy

$$ b^i\le 2^i W_i. $$

Only the stated samples have to be integral or bounded. Values between lattice points can grow arbitrarily large. This includes a cleared integer polynomial divided by its public denominator whenever its sampled values are integers. Each interval may use a different polynomial basis. It also covers the constant column, which must be a nonzero integer on the progression. [Checked column theorem](../PrimeFactors/IntegerLaneWindowWork.lean) · [Mathlib's forward-difference identity](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Algebra/Group/ForwardDiff.lean)

In a window with degrees $0,1,\ldots,k$, choose $b=2J$. If the window contains at least $2Jk+1$ consecutive points of one allowed progression, the sampled points needed for every column fit. Therefore
$V=\prod_{i=0}^k W_i\ge J^B$ for $B=k(k+1)/2$. A sufficient determinant bound for the project methods implies
$N^T V<D^{m(k+1)}$ with $T=m(m+1)/2$, $0\le m\le k$ and $D^2\le N$. Raising to the fourth power and cancelling $N^{4T}$ gives the stronger depth-specific condition

$$ V^4<N^{2m(k-m)}. $$

Because $2m(k-m)\le B$, any integer $J$ with $J^4\ge N$ gives a contradiction. The window can contain at most $2Jk$ consecutive lane points. For a residue class of stride $s$, a contiguous span of candidate indices has strictly fewer than $s(2Jk+1)$ positions, allowing for incomplete ends. With seven rows and depth three, $2m(k-m)=18$ and $B=21$. For every $N\le2^{2048}$ we may take the smaller integer $J=2^{439}$ since $2048\cdot18<439\cdot84$. Each such window covers at most $12\cdot2^{439}$ positions on one eligible lane. [Width, endpoint and degree-six proofs](../PrimeFactors/IntegerLaneWindowWork.lean)

## What was counted

With $s=3$ or $s=105$, every $d=1+2sz$ is odd and coprime to $s$. We counted these public candidates between $L=\lceil N/(2^{1024}-1)\rceil$ and $\lfloor\sqrt N\rfloor$, inclusive. The endpoints account for both factors having at most 1,024 bits and for seeking the smaller one. A window centered differently simply translates this same progression in its local offset. Every window that charges a height for the whole sifted domain must bound its polynomial on this progression wherever it intersects the window. Summing the per-window counts over a cover proves the table. [Finite cover and numerical receipts](../PrimeFactors/IntegerLaneWindowWork.lean)

Here is the exact public arithmetic in the comparison. The lower bounds for the square root and upper bounds for the fourth root come from integer power comparisons. The limits on the method are conditional on the determinant test and the specified geometric coverage. They give no general computational lower bound for factoring.

```python
from pathlib import Path
import re

source = Path("PrimeFactors/ChebyshevQuarticScale.lean").read_text()
for name, low_sqrt, upper_fourth in (("fresh", 57719, 3844), ("crossed", 49228, 3551)):
    n = int(re.search(r"def " + name + r" : ℕ := (\d+)", source)[1])
    lo = (n + 2**1024 - 2)//(2**1024 - 1)
    hi = low_sqrt * 2**1008
    j = upper_fourth * 2**500
    assert hi**2 <= n <= j**4
    for s in (3, 105):
        first = (lo + 2*s - 2)//(2*s)
        last = (hi - 1)//(2*s)
        count = max(0, last+1-first)
        slot_bits = (505 if s == 3 else 500) + (name == "crossed")
        window_bits = (575 if s == 3 else 570) + (name == "crossed")
        assert (2*j)*2**slot_bits < count
        assert (12*2**439)*2**window_bits < count
```
