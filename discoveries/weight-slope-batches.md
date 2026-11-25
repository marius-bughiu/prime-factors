# Reporting weighted sums from two lists of CRT residues

Grouping remainder pairs by their shared slope recovered both prime factors of the 82-bit fixture in 4.42 seconds. The earlier search took 8.63 seconds on the same input with the same weights and final square test. The improvement comes from reporting possible weighted sums directly, saving a visit to each individual remainder pair. On the 2,048-bit control, even visiting one representative of every slope would require more than $2^{585}$ visits. [Previous weighted search](one-trace-per-residue-pair.md) · [Paired measurements](../research/midpoint-slope-batches.json)

## Which slopes must a complete search visit?

For $N=pq$ with odd primes $p<q\le2p$, let $R$ be a public radix coprime to $N$. Write $u=p\bmod R$ and $w=q\bmod R$. Their slope is $s=w/u=N/u^2\bmod R$. The weighted search finds integers $a,b$ with $b\equiv as\pmod R$ and an interval $[L,U]$ of width less than $R^2$ containing the true trace $t=aq+bp$. The low digits determine $t\bmod R^2$, giving at most one value of $t$ per pair. A square discriminant and the original product equality recover the integer factors. All interval and radix choices use $N$ and the balance promise. [Weighted-trace proofs](../PrimeFactors/MidpointWeights.lean)

Write $G=(\mathbb Z/R\mathbb Z)^\times$ and $K=\#\{e\in G:e^2=1\}$. The map $u\mapsto N/u^2$ has fibers of size $K$, so its image has size $\varphi(R)/K$. The solver keeps one orientation of the pair $(u,w)$ by comparing its digits in the prime-power factors of $R$ in order. At the first difference it keeps the orientation whose first digit is smaller. Negating both unit digits replaces $u_i,w_i$ by $m_i-u_i,m_i-w_i$, so it reverses that comparison and preserves all earlier equalities. The negated pair still has product $N$ and exactly the original slope. If all digits tie, the original pair is retained. Consequently the complete canonical scan visits **exactly** $\varphi(R)/K$ slopes. Lean checks the group count, the digit reversal and the representative argument. [Slope fibers](../PrimeFactors/AffineSlopeClasses.lean) · [Canonical orientations](../PrimeFactors/CanonicalWeightSlopes.lean)

At an odd prime power the square roots of one are precisely $\pm1$: the prime divides at most one of $e-1,e+1$. At a power of two there are at most four, since for odd $e$ one of $e-1,e+1$ has valuation exactly one, except for the zero factor when $e=\pm1$ itself. Chinese remaindering therefore gives $K\le 2^{\omega(R)+1}$. Also $\varphi(R)\ge R/2^{\omega(R)}$. As $R\ge (\omega(R)+1)!$, one has $\omega(R)=o(\log R)$ and thus $\varphi(R)/K=R^{1-o(1)}$. The weighted radix is of order $N^{1/3}$, giving a lower bound $N^{1/3-o(1)}$ for searches visiting each slope. Other approaches to factoring can avoid this representation.

The 2,048-bit control uses $R=59\prod_{p\le491}p$, where the product runs over 94 primes. Its dyadic component is 2. The slope count is therefore $59\prod_{p\le491}(p-1)/2^{93}$. Lean checks that $R$ has 682 bits and the slope count lies strictly between $2^{585}$ and $2^{586}$. [Checked finite inequalities](../PrimeFactors/CanonicalWeightSlopes.lean)

## How to report only interval-compatible traces

Factor the public radix into prime powers $m_i$. For a fixed slope $s$, each local unit $x$ satisfies $N/x^2\equiv s\pmod {m_i}$. There are at most four choices per component. A representative lift of each $x$ gives one local trace
$$
T_i(x)=aN/x+bx \pmod {m_i^2}.
$$
Replacing one unit lift by $x'=x+m_i v$ changes its trace by $(x'-x)(b-aN/(xx'))$, a multiple of $m_i^2$ because $b\equiv aN/x^2\pmod {m_i}$. This makes the local calculation independent of all the other digits. The first component with $s\not\equiv1\pmod {m_i}$ is exactly the first place where the pair differs. At that one component keep only canonical local choices. Thus the entire retained fiber is a Cartesian product of small lists.

Merge equal values *within* each local trace list. At any odd prime $\ell\nmid a$ in $R$, the two local sign choices give opposite traces whose reductions are $\pm2bx\ne0\pmod\ell$. They remain distinct. This explains why a common slope and common weights can still produce exponentially many trace residues in the number of radix primes.

Embed each list into $\mathbb Z/R^2\mathbb Z$ using the Chinese remainder theorem. Distinct choices from these reduced lists give distinct global residues. Let $D$ be the product of their sizes. Remove singleton lists into a constant offset. Place each remaining list into the half having the smaller current product of sizes. The ratio of the two half sizes stays at most four, so each half has at most $2\sqrt D$ entries. Generate both lists of sums and sort the second. Include the singleton offset and subtract $L$ in the first list, then reduce its entries to $0\le x<R^2$. For $y$ in the second list, let $W=U-L$. The trace lies in the interval exactly when
$$
x+y\le W \quad\text{or}\quad R^2\le x+y\le R^2+W .
$$
Two binary searches per window report its members. Each yields one trace $L+((x+y)\bmod R^2)$. If its quadratic gives an integer divisor, the implementation checks the factor balance, product, slope and canonical orientation. This preserves the meaning of partial searches too. [Two-window proof](../PrimeFactors/CanonicalWeightSlopes.lean) · [Solver](../experiments/midpoint_slope_batches.py) · [Exhaustive short tests](../tests/test_midpoint_slope_batches.py)

After local tables and weights are available, a slope with $k$ prime-power components and $Y$ reported traces takes $O(k\log(2k)+\sqrt D\log(2D)+Y)$ comparisons and arithmetic operations on integers with $O(\log N)$ bits, including an integer square root for each eligible output. The table construction scans each local modulus once and performs a modular inverse per local unit. There can still be many output traces. A budget on half-list entries is checked before allocating either list.

## Measured work

The eight 49–50-bit holdout products use the same 25-bit prime streams as the earlier comparison. Every method received the product and its public parameters. Each recovered the expected prime pair. Five repetitions per input rotate the order of the five methods. The final column sums the eight individual medians of discovery time on arm64 macOS 27.0.1 with CPython 3.9.6. A radix multiplier enlarges the public base $R$ while preserving the balance bound. [Experiment](../experiments/midpoint_slope_holdout.py) · [All timings and factors](../research/midpoint-slope-batches.json)

| Evaluation | Slope visits | Half-list entries | Candidate sums | Integer square roots | Seconds |
| --- | ---: | ---: | ---: | ---: | ---: |
| Ordinary pair visits, base $R$ | 2,280 | — | 23,956 | 20,337 | 0.06145 |
| Two lists, base $R$ | 2,280 | 18,478 | 21,734 | 18,456 | 0.05191 |
| Two lists, base $2R$ | 2,580 | 29,158 | 15,619 | 13,517 | 0.05879 |
| Two lists, base $3R$ | 6,840 | 56,258 | 13,081 | 11,194 | 0.12502 |
| Two lists, base $4R$ | 4,500 | 52,774 | 10,747 | 9,218 | 0.09148 |

Base $R$ had the lowest median time on each of the eight inputs. A larger base eliminated additional square tests while increasing list and slope costs. Both implementations used the ordinary integer square test for this comparison. [Separate reduced-discriminant experiment](reduced-weight-discriminants.md)

On $3043806426885490749164321=1688035255729\cdot1803165198449$, the ordinary search visited 7,188,480 remainder pairs and performed 3,695,517 square tests. The two-list method used 1,241,556 half entries across 56,160 slopes and performed 3,261,252 square tests. The respective 8.63 and 4.42 second times are medians of three alternating runs. The benchmark separately checks the primes and their product in Lean. On the crossed 2,048-bit input the first slope alone requested a list of $2^{46}$ entries. With a 65,536-entry cap, the solver completed zero slopes and left the full product unresolved. [Benchmark fixtures](../benchmarks/midpoint-slope-batches.json)
