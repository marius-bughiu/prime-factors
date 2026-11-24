# How many product bits does the factor count need?

Suppose a multiplier accepts candidate factors $x,y$ when $xy=N$. Can we remove its highest output columns and still recover the same information about the factors? There are two exact ways to do this. For balanced factors, a window on a weighted sum can replace the missing columns. For any bounded factors, a comparison involving their leading bits suffices. Removing the columns alone can destroy even the lowest bit of the answer. The question matters because the cost of constructing or contracting this multiplier dominates the [quarter-width count](quarter-width-count.md).

## What goes wrong with plain truncation

Take $1<x\le y<2^b$ and replace $xy=N$ by $xy\equiv N\pmod{2^m}$. Every surviving pair contributes $y\bmod2^k$ witnesses. For every odd target, every $2\le m<b$ and every $k\ge1$, the total is **even**. For an odd semiprime with both factors in the box, the exact total is odd. The two answers therefore disagree even after reduction modulo $2^k$. In the proof, matching off-diagonal terms cancel in pairs modulo two. A second pairing handles the diagonal. For $77=7\cdot11$ in a four-bit box, retaining three product bits gives 30 witnesses. Their residue modulo eight is 6, while exact multiplication gives 3. [Lean proof and checked example](../PrimeFactors/TruncatedProduct.lean)

Failures also occur above this threshold. Among all 1,718 pairs of distinct ten-bit primes with a 20-bit product, keeping 19 product bits gave the correct five-bit residue for 1,023 pairs. At 18 bits it gave 649 correct residues and at nine bits it gave zero. The experiment first tabulates all odd ordered candidates, including composite candidates, then uses the primes only to score the resulting residues. [Reproduce the complete sweep](../experiments/truncated_product.py)

## Weighted sums for balanced factors

Assume $0<x\le y\le2x$ and $N<2^n$. A single sum window $4N\le (x+y)^2\le9N/2$ and the low-product check $xy\equiv N\pmod M$ together force $xy=N$ when $8M>N$. This permits dropping three leading output bits.

A single interval with fixed weights improves that to **five leading bits**. The coefficients 17 and 12 approximate the middle of the ratio range on a logarithmic scale. Throughout $x\le y\le2x$, Lean proves $8(17x-12y)^2\le204xy$. For $N<32M$ we therefore have $xy=N$ exactly when the low product matches and

$$\lceil\sqrt{816N}\rceil\le17x+12y\le\left\lfloor\sqrt{6732N/8}\right\rfloor.$$

Both ends depend only on $N$. Multiplication by 17 uses one shift and an addition, and multiplication by 12 uses two shifted terms. This version handles the entire factor ratio range with one interval.

Five bits is the most this single-window **uniform error estimate** can guarantee over the full real ratio range. For slope $t=a/b>0$ and ratio $r=y/x$, the normalized squared gap is $t/r+r/t-2$. The larger endpoint value at $r=1,2$ is minimized at $t=\sqrt2$, where it equals $3/\sqrt2-2$. Indeed for $t\le\sqrt2$ the endpoint $r=2$ dominates and decreases with $t$, and above $\sqrt2$ the endpoint $r=1$ dominates and increases. Thus the factor multiplying $M$ in this estimate can approach $4/(3/\sqrt2-2)\approx32.97$. Six omitted bits would require a factor of 64.

For a narrower window choose a positive integer $R$ and round $Ry/x$ to its nearest integer $a$. Then $R\le a\le2R$ and $2|ax-Ry|\le x$. Put $K=4R^2$ and $S=ax+Ry$. The identity

$$S^2=4aRxy+(ax-Ry)^2$$

puts $S$ in the interval specified by $4aRxy\le S^2$ and $KS^2\le(4K+1)aRxy$. Require the same inequalities with the public target $N$ in place of $xy$. Comparing the two sets of inequalities gives $4K|xy-N|\le N$. Thus $16R^2M>N$ makes equal low products sufficient for equality. Both endpoints for $S$ are precomputable integer square roots. For each public $a$, the remaining tests on $x,y$ are linear comparisons with constant coefficients. For odd $x$ the nearest integer has no ties. A general counting implementation should resolve ties once or take a Boolean union of the tests. [Lean endpoints, error bound, floor and nearest variants](../PrimeFactors/TruncatedWindow.lean) · [Earlier weighted-square divisor intervals](searching-the-balanced-interval.md#one-square-test-for-a-divisor-interval)

At $R=2^t$ we can omit $2t+4$ bits when $n\ge 2t+4$. For a 2048-bit balanced target, $R=1024$ leaves **2,024 product bits and 1,025 possible weighted-sum windows**. Each trial slope carries the cost of its comparisons. In a schoolbook multiplier of two $b$-bit inputs, omitting the top $s\le b$ product bits saves only $s(s-1)/2$ bit products before guard overhead, plus carry logic. At $b=1024$ and $s=24$ this removes 276 of 1,048,576 bit products. The theorem prices a trade between constraints. Its effect on total contraction time at this width is open.

## A leading-bits test for any bounded factors

For $0\le x,y<2^b$, omit $s$ of the $2b$ product bits, where $0<s<b$. Set $h=s+1$, $L=2^{b-h}$ and $M=2^{2b-s}$. The leading $h$ bits of $x,y$ give $a=\lfloor x/L\rfloor$ and $c=\lfloor y/L\rfloor$. Then

$$acL^2\le xy<(a+1)(c+1)L^2.$$

The width is $(a+c+1)L^2<M$. If $xy\equiv N\pmod M$, the interval contains $N$ exactly when $xy=N$. This preserves every accepted pair, so it works for composite candidates, unequal widths padded to the bound, and targets with many factorizations. A direct table tests $2^{2h}$ prefix patterns. One could instead implement an $h$-bit multiplication and use $ac+a+c+1$ for the upper endpoint. [Lean proof](../PrimeFactors/ProductPrefix.lean)

The experiment deletes the missing-product columns and carry wires, builds the small prefix table, and runs the same elimination rule with the same ordering and counter predicates. The table gives **total compatible row joins** for all products of distinct primes of the indicated factor width. Table construction is extra and scans $4^{s+1}$ prefix patterns per product for $s>0$.

| Factor bits | Products | Full multiplier | Drop 1 | Drop 2 | Drop 3 |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 1 | 710 | 780 | 749 | 630 |
| 5 | 10 | 19,154 | 22,928 | 17,668 | 16,203 |
| 6 | 21 | 100,187 | 113,671 | 132,574 | 166,475 |

Dropping three improved the join count on all ten five-bit products and on none of the 21 six-bit products. The peak table size never fell in this sweep. For $323=17\cdot19$, joins fell from 2,158 to 1,599, with 256 prefix patterns inspected. This measures a saving on a finite family for a specified elimination rule. A wall-clock improvement at larger widths requires evidence. Run the comparison with `python3 experiments/guarded_product.py --sweep`. [Experiment and cost counters](../experiments/guarded_product.py)
