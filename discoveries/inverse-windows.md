# When a low product word rules out a pair of factor intervals

Let $X$ be a power of two, and let $N=pq$ for distinct primes in $[X,2X)$. Partition the two factor ranges into aligned intervals of length $L$. Read the low product word $a=N\bmod M$, where $L\le M\le X$ are powers of two. Discard a rectangle if it contains no odd integer pair with $xy\equiv a\pmod M$. For **typical prime products**, the transition in how many geometrically possible rectangles survive occurs at side length $\sqrt M$, up to subpower factors. With $M=X$ and any fixed $\delta>0$, almost every candidate rectangle can be discarded below $L=X^{1/2-\delta}$, and almost none above $L=X^{1/2+\delta}$. The point-counting identity, the cost of locating these rectangles and the precise sampling statement follow below. [Lean counts and symmetries](../PrimeFactors/InverseWindows.lean) · [Bounded experiment](../experiments/inverse_windows.py)

## An exact second moment for a translated window

Choose $a$ uniformly over the odd residues modulo $M$ and choose a cyclic interval $J$ of length $L$ with independently uniform start. Fix $n$ odd source values whose residues modulo $L$ are distinct. Let $Z$ count their partners $a/x\bmod M$ in $J$. Each has probability $P=L/M$ of landing in the interval, and **every pair of these membership events is independent**. Consequently
$$\mathbb EZ=nP=\mu,\qquad \operatorname{Var}(Z)=nP(1-P).$$

For two different sources write their inverse-coordinate difference as $r s\bmod M$, where $r$ is its exact power of two and $s$ is odd. Dividing $x-y$ by the unit $xy$ preserves its dyadic valuation, so $2r\mid L$. As $a=2h+1$ varies, the partner difference runs uniformly over residues congruent to $r$ modulo $2r$. Fix the first partner's location $u\in[0,L)$ relative to the start. For each $a$ this determines exactly one start. The possible second locations hit every residue in one class modulo $2r$ equally often. Exactly $L/(2r)$ positions of this class lie in the window and each has $r$ preimages among the $M/2$ odd words. Thus $L/2$ choices of $a$ work for each of the $L$ possible $u$, giving $L^2/2$ successful word/start pairs out of $M^2/2$. This proves the joint probability $P^2$. Lean proves this finite count as a sum over the odd multiplier and first local offset. Higher joint independence is unnecessary. Related results on averages of modular inverses and translated windows treat more general moduli. [Shparlinski](https://arxiv.org/abs/math/0608596) · [Chan, Theorem 1](https://arxiv.org/abs/0812.1526)

For a square of side $L$ the source interval has $n=L/2$ odd entries. Thus the empty probability is at most $(1-P)/(\mu+1-P)$ by Cauchy–Schwarz applied to $Z$ on its positive outcomes. In the opposite regime the occupied probability is between $\mu-\binom n2P^2$ and $\mu$ by inclusion–exclusion. Exact independence uses the random start. With $M=64,L=4$ and both intervals aligned, the second factorial moment averaged over all cells and odd words is $1/64$, double the translated value of $1/128$.

## From arbitrary placements to the actual prime products

For an aligned $L$-cell with a uniformly chosen column among the $M/L$ columns, let $P_0$ denote its probability of being empty, still choosing a uniform odd product word. For $L\ge4$, retain the first $L/2$ source positions and slide a target window of length $L/2$ through the first $L/2$ target starts in that cell. An empty large cell makes every such smaller window empty. Over all aligned columns these starts comprise exactly half of the cyclic starts. The smaller window has mean $L^2/(8M)$, so the translated estimate gives $P_0\le\min(1,16M/L^2)$. This bound is uniform in the source interval. The factor 16 here includes both restricting the start and halving both side lengths.

An actual product selects its geometry and its word together. Call a rectangle geometrically possible when its endpoint product range contains $N$, allowing the order $p\le q$ to restrict the candidate set. For each physical rectangle, this product range has length at most $4XL$, by expanding the difference of its corner products. It can therefore contain at most $1+4XL/M$ distinct integers in any one residue class. Different unordered prime pairs have different products. Since $M\mid X$, the physical rectangle grid repeats the complete residue grid. Summing the number of offending words over rectangles gives at most
$$(X/L)^2\,(M/2)\,P_0\,(1+4XL/M)$$
incidences of a prime product and an empty geometrically possible rectangle. Here $P_0$ may be taken as the preceding uniform upper bound. There are order $X^2/(\log X)^2$ distinct prime products by the prime number theorem. The expected number of discarded rectangles divided by $X/L$ is therefore $O(M(\log X)^2/L^2)$. This argument uses the number of integers in each geometric range and makes no independence assumption about the actual prime factors.

For the other direction, every modular witness in a geometrically possible rectangle satisfies $xy=N+jM$ with $|jM|\le4XL$. Each of these at most $1+2\lfloor4XL/M\rfloor$ positive lifted products has at most $X^{o(1)}$ positive divisors, uniformly for $xy\le4X^2$. Its first divisor identifies the ordered pair, and each pair belongs to a unique rectangle. Hence the total number of surviving rectangles is $O((1+XL/M)X^{o(1)})$ **for each input**. The Lean proof injects the witnesses in a thin product interval into the divisors of its lifted products. [Divisor estimate](modular-hyperbola.md)

For $N/X^2$ in a fixed compact subinterval of $(1,4)$, the admissible smaller-factor range has length $\sqrt N-\max(X,N/(2X))\asymp X$. For $4\le L=o(X)$ each full interior row contains a candidate rectangle, and each row meets $O(1)$ columns, giving $\asymp X/L$ geometrically possible rectangles. Thus for $M=X$ the narrow bound gives a surviving fraction tending to zero uniformly in that interior range. In the wide regime Markov's inequality gives a discarded fraction tending to zero in probability. The same typical conclusions hold over the full prime-pair population: the chance that the normalized product is within $\eta$ of either endpoint is $O(\eta^2)$ in the limit, by applying the prime number theorem to the endpoint intervals for both factors. Take fixed $\eta$ first, then let it decrease to zero. For general $M\le X$ the displayed bounds give the corresponding transition whenever $L^2/M\le X^{-\delta}$ or $L/(\sqrt M\log X)\to\infty$. Bounds for individual products with a prime auxiliary modulus are a separate question. [Prime-modulus box bounds](hyperbola-boxes.md)

## Querying the occupied cells

Build a table of inverse points by their two residue blocks. When $64\mid M$, put $H=M/8$. The translation
$$(x,y)\longmapsto (x+H,y-aH)\pmod M$$
preserves $xy=a$. To check it, expand the product and use $H^2=0\bmod M$ and $x^2=1\bmod8$ for odd $x$. If $L\mid H$, translating respects block boundaries. It suffices to store the $M/16$ odd sources below $H$ and their partners; rotating a query returns every witness in its physical rectangle. This is the maximal saving by a *global translation* of the graph. Indeed a preserving translation $(h,k)$ must satisfy $kx(x+h)=-ah\bmod M$ for every odd $x$. Taking $x=1$ shows that $h$ and $k$ have equal dyadic valuation for a nonzero translation. If $h=2\bmod4$, subtracting the $x=1$ equation from $x=3$ gives $M\mid k(8+2h)$, impossible for $64\mid M$. If $4\mid h$, using $x=5$ gives $M\mid k(24+4h)$, hence $M/8\mid k$ and $M/8\mid h$. The eight exhibited translations attain the bound.

A complete search in the bit-width box now needs $O(X/L)$ rectangle lookups, $O(M)$ stored residues, and at most $O((1+XL/M)X^{o(1)})$ reported pairs to verify by multiplication. Sorting the table by block and using binary search gives deterministic polylogarithmic overhead; the Python demonstration uses dictionary buckets. Setting $L$ near $X^{1/3}$ and $M$ near $X^{2/3}$ gives deterministic $X^{2/3+o(1)}=N^{1/3+o(1)}$ bit operations. This matches the earlier affine-window exponent with more storage. At a very large modulus, a geometric rectangle whose product span is less than $M$ can admit only the true integer product. The cost of constructing its membership information is then essential. [Earlier polynomial-space search](modular-hyperbola.md) · [Lehman](https://doi.org/10.1090/S0025-5718-1974-0340163-2)

## Complete bounded comparisons

For all 9,316 pairs of distinct 11-bit primes, $L=16$ gives 352,655 geometrically possible cells across the whole population. The baseline performs 1,397,727 odd trial divisions within the same factor-width box.

| $M$ | Surviving cells | Candidate products | Table entries per word | Products to build all distinct words' tables |
| ---: | ---: | ---: | ---: | ---: |
| 64 | 255,227 | 713,650 | 32 | 1,024 |
| 256 | 131,103 | 186,597 | 16 | 2,048 |
| 1,024 | 48,385 | 53,264 | 64 | 32,768 |
| 4,096 | 19,586 | 20,169 | 256 | 517,888 |
| 16,384 | 11,464 | 11,618 | 1,024 | 5,742,592 |

Inversions of the table's odd sources can be shared across all words at one modulus. The last column also shares tables across equal product words. With $M=1024$, an independent table for each product would cost 596,224 modular multiplications. Preparation and bucket queries took about 0.25 seconds across the population, against 0.04 seconds for the complete trial baseline in CPython 3.9.6 on arm64. At $M=64$, $L>M/8$ and the implementation uses the full point table.

The 62-bit comparison reuses two primes from existing fixtures to form $N=3221225472647483647$. The search receives the product and the promise of 31-bit factors. This single timing measures a deliberately selected input. At $L=1024,M=2^{20}$, 65,536 modular inversions and table entries, 631,090 cell queries, and 315,398 witness products recover $1500000001\cdot2147483647$. The complete run took 0.073 seconds for preparation and 0.664 seconds for queries, against 9.17 seconds for 147,388,638 odd trial divisions. Lean checked the factorization generated from the returned pair. These are single-machine observations.

```sh
python3 experiments/inverse_windows.py 11 4 10
python3 experiments/inverse_windows.py 9 4 8 --moments
python3 experiments/inverse_windows.py 31 10 20 --product 3221225472647483647 --compare-trial
```
