# When to stop counting factor sums

On both 2,048-bit comparison products, counting **one midpoint** was enough to prove that no later midpoint fits more odd integer pairs. The ranking setup fell from 25 square roots to 3 on the independently generated product and from 49 to 3 on the crossed product. The winning sums stayed the same. Testing each against its product left both numbers unfactored. [Four benchmark cases](../benchmarks/high-word-suffix-ranking.json) · [Reproducible comparison](../experiments/word_ranking_tail.py)

## The stopping inequality

The high word puts the product in a known interval $[n,T]$ of width $w=T-n$. A midpoint $u$ and a positive half-gap $v$ represent the pair $(u-v,u+v)$, whose product is $u^2-v^2$. The known remainder and odd-factor requirement allow only certain half-gap residues modulo $P=\operatorname{lcm}(2,m)$, where $m$ is the remainder modulus. Let $K$ be the maximum number of allowed half-gap residues at any midpoint residue in one whole period. [How the rows and residue table are formed](choosing-a-sum-from-a-word-and-a-remainder.md)

Suppose an earlier midpoint already contains $c$ pairs. At the next eligible midpoint $j$, set $H=P\lfloor c/K\rfloor$ and $d=\max(0,j^2-T)$. If $K>0$, $H>0$ and either inequality below holds, **every midpoint $u\ge j$ contains at most $c$ pairs**. Ties keep the earlier midpoint.

$$
 w<H^2
 \qquad\text{or, when }w\ge H^2,\qquad
 (w-H^2)^2<4H^2d.
$$

To see why, suppose a later row contains two gaps at least $H$ apart, the smaller one being $v$. The difference between their squares is at least $2Hv+H^2$ and at most $w$. Also $v^2\ge d$. Either stopping inequality contradicts these bounds. All the row's gaps therefore fit within fewer than $H$ units from first to last. Partitioning from the first gap into $\lfloor c/K\rfloor$ blocks of $P$ consecutive integers gives at most $K\lfloor c/K\rfloor\le c$ pairs. If fewer than $K$ pairs have been found, this test cannot stop the search. The bound applies to arbitrarily late rows. The usual prefix search supplies the separate argument excluding midpoints before the first inspected row. [Lean stopping theorem for physical pairs](../PrimeFactors/WordRankingTail.lean) · [Prefix bound](../PrimeFactors/HighWordSuffixRanking.lean)

## Work on the four benchmark inputs

All four inputs used modulus 120. The two 66-bit products deliberately share their high word and remainder, so the ranking computes the same counts on both. The checker compares the selected midpoint **and its exact count** against the original search over all 121 positions, then performs one final square test on the actual product. Run `python3 -m experiments.word_ranking_tail` from the repository root. [Checker](../experiments/word_ranking_tail.py)

| Product | Setup roots before → after | Residue classes counted before → after | Stopping tests attempted | Final square test |
| --- | ---: | ---: | ---: | --- |
| 66-bit ranked hit | 25 → 5 | 64 → 12 | 2 | Recovered 6,073,583,363 |
| 66-bit ranked miss | 25 → 5 | 64 → 12 | 2 | Whole product unresolved |
| 2,048-bit independently generated | 25 → 3 | 64 → 4 | 1 | Whole product unresolved |
| 2,048-bit crossed | 49 → 3 | 64 → 4 | 1 | Whole product unresolved |

The first skipped midpoint was $\lfloor\sqrt T\rfloor+21$ on the 66-bit inputs, $\lfloor\sqrt T\rfloor+19$ on the independently generated input, and $\lfloor\sqrt T\rfloor+3$ on the crossed input. The maximum residue count $K$ was eight on the first three inputs and four on the crossed input.

Each attempted stopping test here computed three squares, $H^2$, $j^2$ and $(w-H^2)^2$, and one product $H^2d$. The final factor of four is a bit shift. On each full-size input two squares had 1,024-bit operands. The square of $H$ had a 509- or 511-bit operand, and the last multiplication used operands between 1,018 and 1,029 bits. Forming $H$ also used one division by the small class count $K$ and one multiplication by 120. The 66-bit cases each paid for two attempts, eight square or product operations in total plus those small-operand operations. The checker groups 120 possible half-gap residues by their squares and checks all 120 midpoint residues to obtain $K$. These savings reduce the cost of selecting the same sum for the final factoring test. [Checker with per-operation operand widths](../experiments/word_ranking_tail.py)
