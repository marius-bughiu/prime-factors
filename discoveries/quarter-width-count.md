# A quarter-width count for the larger prime

Let $N=pq$ have $n$ bits, with distinct odd primes $p<q$. Set $k=\lceil n/4\rceil$ and $M=2^k$. From the public product, form the following counting problem on bounded integers:
$$
1<x\le y<2^n,\qquad xy=N,\qquad 0\le t<(y\bmod M).
$$
The count is exactly $q\bmod M$. Only the pair $(p,q)$ passes the first two conditions. It permits exactly as many values of $t$ as the residue itself. Since the count is less than $M$, counting modulo $M$ gives the ordinary integer answer with no wraparound. For a 2048-bit input this is **one 512-bit result**, regardless of the relative sizes of the primes. Measuring the cost of computing those 512 bits is essential. [Lean count and examples](../PrimeFactors/LowFactorBits.lean)

## Why the residue suffices

The postprocessing uses the classical small-root theorem for an unknown divisor. If $r=q\bmod M$, write $q=r+Mu$. Since $N$ is odd, $M$ is invertible modulo $N$. The unknown $u$ is a root of the monic linear polynomial $X+rM^{-1}$ modulo the unknown divisor $q$. May's Theorem 7 finds the roots of this kind in polynomial time when $q\ge N^\beta$ and $|u|\le cN^{\beta^2}$ for constant $c$. Candidate integers are checked by multiplication or divisibility. [May, Theorems 6–7 and the least-significant-bit example](https://digital.ub.uni-paderborn.de/hsmig/download/pdf/3235#page=38)

For balanced primes, $q\ge\sqrt N$ and $q\le\sqrt{2N}$. Taking $\beta=1/2$ and $M\ge N^{1/4}$ gives $u<\sqrt2 N^{1/4}$. The constant factor is allowed at the endpoint of the published bound.

For arbitrary sizes, try each possible integer $a=\lfloor\log_2 q\rfloor$. Put $\beta=a/n$. For the correct guess,
$$
N^\beta\le 2^a\le q<2^{a+1}\le4N^\beta,\qquad
0\le u<4N^{\beta-1/4}\le4N^{\beta^2}.
$$
The final inequality is $(\beta-1/2)^2\ge0$. There are at most $n$ guesses and the constants can be chosen uniformly. In May's degree-one proof, for $n\ge7$ one may take $\epsilon=1/n$, lattice parameter $m=a$ and dimension $n$. The small-root radius before the constant number of interval shifts is at least $N^{\beta^2}/4$. Smaller inputs form a bounded set. The counting identity is local Lean work. This polynomial-time decoding argument invokes May's theorem on paper. The stated output width is sufficient; it is not a lower bound on every factoring method.

## Cost of producing the count

Start with a parsimonious multiplier, where each ordered factor pair has one internal filling. Add a comparison for $1<x\le y$ and compare the $k$ free bits of $t$ with the lowest $k$ bits of $y$. Each comparison uses a chain of Boolean gates with uniquely determined state. The multiplier theorem used by Shunia has $O(n)$ edges and maximum degree $O(n^{3/4})$. The added comparisons and wire copies have $O(n)$ edges and bounded degree. After equality subdivision, Theorem D.1 applies to this bipartite network over the ordinary ring $\mathbb Z/2^k\mathbb Z$. Its published deterministic upper bound is $2^{O(n/\sqrt{\log n})}$ bit operations and polynomial space. The change from the published prefix algorithm is one nonadaptive contraction at quarter-width output precision. It preserves the known exponent and gives no practical runtime bound at a particular input size. [Multiplier and existing prefix method](https://hexagonmath.org/pdf/2610.00711v1) · [Quantitative Boolean tensor contraction](https://github.com/openai/math/blob/main/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-reduction.tex)

The count and the decoder have different costs. Adding $t$ and its comparator can make a particular contraction schedule more expensive even while reducing its number of calls and its output width. For $N=143$, $k=2$ and the ordered nontrivial pair is $(11,13)$. Only $t=0$ passes, yielding residue 1. Many candidate integers share that residue; the product enters the lattice step as well. The same construction for $N=51$ gives $17\bmod4=1$.

## Measuring the count on small products

The experiment builds a schoolbook multiplier with pinned product bits, then adds ordinary Boolean comparators. All intermediate comparison states are uniquely determined by their inputs. It sums local constraint tables modulo $2^k$, without supplying either prime. Its output is the residue and a record of the work. [Experiment](../experiments/quarter_residue.py) · [Inputs and controls](../benchmarks/quarter-residues.json)

| Input | Box | Output | Compatible row joins | Peak table rows |
| --- | --- | --- | ---: | ---: |
| 143 | Full, 8 bits per factor | 1 modulo 4 | 61,315 | 32,896 |
| 51 | Full, 6 bits per factor | 1 modulo 4 | 4,783 | 2,080 |
| 77 | Full, 7 bits per factor | 3 modulo 4 | 24,009 | 8,256 |
| 667 | Balanced bound, 6 bits per factor | 5 modulo 8 | 5,555 | 2,080 |

The deliberately undersized four-bit box for 51 returns zero because 17 lies outside it. The displayed costs belong to this small elimination implementation. The lattice decoder and the published asymptotic contraction algorithm were not timed. Run the bounded experiment with the following command.

~~~sh
python3 experiments/quarter_residue.py --fixtures
python3 experiments/quarter_residue.py 143 --compare-bits --unit-tags
~~~

Another way of obtaining the residue removes the auxiliary $t$ register from the graph. Retain the ordering and give each bit of $y$ an independent weight, whose product is
$$
W(y)=(-1)^{\lfloor y/2\rfloor\bmod2}5^{\lfloor y/4\rfloor}\pmod{2^k}.
$$
For an odd prime $q$ and $k\ge2$, the single surviving pair returns $W(q)$. Its value modulo four gives the sign. After removing the sign, repeated squaring lifts the exponent one bit at a time, recovering $q\bmod2^k$ in $k-2$ squarings and at most $k-2$ additional modular multiplications. The weights attach to existing inputs and add no Boolean comparison gates. For $12827=101\cdot127$, one contraction returns $3$ modulo 16. The decoder returns $15=127\bmod16$. [Lean encoding and decoder](../PrimeFactors/DyadicReadout.lean)

To compare actual work, pin each low bit of $y$ to one in a separate copy of the ordered graph and add up the row joins across independent eliminations. Since $q$ is odd, a competitive control can skip its lowest bit. The counts below include that version. All four methods have the same peak table size within each row. These independent queries do not share intermediate tables.

| Input and box | Slack count | Signed weights | All $k$ bit queries | $k-1$ queries using oddness |
| --- | ---: | ---: | ---: | ---: |
| 51, full | 4,783 | 4,743 | 9,516 | 4,743 |
| 77, full | 24,009 | 23,995 | 47,997 | 23,998 |
| 143, full | 61,315 | 61,177 | 122,482 | 61,177 |
| 667, balanced | 5,555 | 5,660 | 17,015 | 11,325 |
| 12827, balanced | 66,488 | 66,312 | 265,394 | 198,954 |

Removing the slack comparator saves 176 joins on 12827 and adds 105 on 667. The changed elimination order matters even when the output equals the same residue. A separate experiment measures what happens when leading product bits are removed from this network. [Exact guards and measurements](truncated-products.md)

There is a second comparison at identical input widths. The ternary reverse-sweep experiment finds the **whole factor sum** without the ordering and slack comparators. On 143 its full-width network used 24,025 joins and peaked at 4,096 rows. On 667 the balanced network used 4,438 joins and peaked at 1,176 rows. At these sizes the smaller output of the quarter-width method costs more construction work than the ternary readout. [Ternary construction and measurements](counting-the-factor-sum.md)

The same small-root theorem permits a precision/work tradeoff. Guessing $d$ additional low bits costs at most $2^d$ candidate residues. Saving a fixed multiple of $\log_2 n$ counted bits therefore retains a polynomial decoder, with a correspondingly larger polynomial. A different construction keeps the multiplication graph intact and tags both of its inputs with ordinary modular weights. [Weighted readout and its RH-based choice of modulus](exponential-readout.md)
