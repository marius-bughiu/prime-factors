# Selecting coordinates from an interval of possible factors

Suppose two distinct 1,024-bit primes multiply to the given number. If we know an interval of width $2^{510}$ containing the smaller prime, one calculation gives **at most three pairs of search coordinates**. One pair leads to a factor somewhere along its row. We still have to find the interval and the successful position on that row. Both full-size examples have more than $2^{510}$ intervals in our public partition. [Lean coverage theorem](../PrimeFactors/OffsetCoordinateMultiplicity.lean) · [Benchmark inputs and budgets](../benchmarks/offset-factor-blocks.json)

## Why three pairs suffice

Write $N=pq$ with $p<q$, choose $T=\lfloor\sqrt N\rfloor-1$, and set $H=N-T^2$ and $J=\lfloor\sqrt{4H/3}\rfloor$. The earlier proof guarantees a pair of coprime integers $0<v\le s\le2v$ such that $j=ps^2-2Tsv+qv^2\le J$. At that pair the trace $2Tsv+j$ reveals a factor by a square test. The coefficients $p,q$ of this form are unknown. [Shifted search theorem](../PrimeFactors/ShiftedOffsetBase.lean)

For a possible value $d$ of the smaller prime, use the form

$$R_d(s,v)=(ds-Tv)^2+Hv^2.$$

This is computable from $d$ and the product. At the true factor, $R_p(s,v)=pj$. For general trials the wider inequality $3R_d(s,v)^2\le4d^2H$ includes every true short vector. Consider a whole block $c-B\le d\le c$ with $16B^2\le H$. Moving from $d$ to $c$ changes $ds-Tv$ by $(c-d)s$, whose square is at most $Hv^2/4$. It follows that $3R_c\le5R_d$, hence $R_c^2<4c^2H$. The same form at the public endpoint $c$ now bounds every candidate in the block. For all target products the shifted remainder satisfies $16(2^{510})^2\le H$. Width here means the difference of the endpoints. [Endpoint bound and target width](../PrimeFactors/OffsetCoordinateMultiplicity.lean)

Reduce the binary quadratic form $R_c$ once. Its determinant is $c^2H$. If $u,w$ are the resulting basis vectors, the only primitive directions whose squared norms $R_c$ satisfy $R_c^2<4c^2H$ are among $u$, $w$ and the shorter of $u+w,u-w$, up to sign. The strict inequality excludes both diagonals when they have equal length. The reduction uses integer arithmetic at $c$ and does not enumerate the integers in the block. Lean proves existence of the reduced basis, the three-direction bound, and that the correct block contains a direction at which the earlier factor test succeeds. [Lean proof](../PrimeFactors/OffsetCoordinateMultiplicity.lean) · [Classical binary form reduction](https://www.wstein.org/edu/124/lectures/lecture23/lecture23/node1.html)

The search can narrow each direction to an exact interval of trial integers. Since $p,q$ are odd, $j$ has the parity of $s+v$. Let $J'$ be the largest integer at most $J$ of that parity, and put $C=2Tsv+J'$. The condition $R_d\le dJ'$ becomes $s^2d^2-Cd+Nv^2\le0$. If the discriminant is negative the direction is empty. Otherwise, with $z=\lfloor\sqrt{C^2-4N(sv)^2}\rfloor$, the bounds are $\lceil(C-z)/(2s^2)\rceil$ and $\lfloor(C+z)/(2s^2)\rfloor$, clipped to the block. These bounds price a necessary inequality. Inside their interval a trial integer may still fail to divide $N$. [Selector and interval calculation](../experiments/offset_factor_blocks.py) · [Independent enumeration tests](../tests/test_offset_factor_blocks.py)

For $N=129133$, the bound of three is sharp even if each trial must itself be prime and satisfy the rounded, parity-adjusted inequality. In the block $[262,269]$, the true factor 263 gives offset 35 in each of the directions $(3,2)$ and $(4,3)$. The third direction $(1,1)$ still allows the prime 269, which does not divide the input. Lean checks the arithmetic and primality. [Prime-trial example](../PrimeFactors/OffsetCoordinateMultiplicity.lean)

Conversely, on $N=122821$ the block $[256,258]$ is empty after the parity test, even though it contains the prime 257. The full search recovers $263\times467$. On the 49-bit comparison the shifted partition covers 2,884 blocks in 12,897 reduction iterations. After deduplication, 292 coordinate pairs remain. The search takes 1,831 offset tests to exhaust those pairs and recover $17{,}838{,}631\times28{,}141{,}469$. Each reported factorization has a Lean certificate. [Worked small example](https://marius-bughiu.github.io/prime-factors/#offset-factor-blocks-three-directions-122821) · [49-bit result](https://marius-bughiu.github.io/prime-factors/#offset-factor-blocks-49)

## When one calculation covers many blocks

There is also a condition that uses only the product and can cover a long stretch of the factor range. Choose a primitive positive direction $u=(a,b)$. At a trial $d$, the Gram determinant identity gives

$$R_d(u)R_d(w)-\langle u,w\rangle_d^2=d^2H\det(u,w)^2.$$

If $J R_d(u)<dH$ and a candidate $w$ satisfies $R_d(w)\le dJ$, the right hand side is strictly less than $d^2H$. Hence the integer $\det(u,w)$ is zero. Primitivity and the positive orientation force $w=u$. The conclusion also holds when the trial has no candidate. One such direction can therefore stand for every block on which the strict inequality holds. [Determinant proof](../PrimeFactors/OffsetCoordinateMultiplicity.lean) · [Implemented comparison](../experiments/offset_factor_blocks.py)

For fixed $(a,b)$ the strict condition is the quadratic inequality $Ja^2d^2-(2JaTb+H)d+JNb^2<0$. Its integer solutions form one interval, with endpoints from one integer square root. The scanner tests directions at the beginning of a block and jumps across every subsequent complete block certified by the same interval. The final clipped block is included if its endpoint passes. It counts reductions, guide tests, the blocks covered and the positions actually checked. [Exact endpoint implementation](../experiments/offset_factor_blocks.py)

For **every** product of two distinct 1,024-bit primes, $(1,1)$ passes the strict test throughout $[\lfloor\sqrt N\rfloor-2^{767},\lfloor\sqrt N\rfloor]$. Intersect this with the public range for the smaller factor. Here $R_d(1,1)=(d-T)^2+H$, and the shifted remainder is large enough that $J((d-T)^2+H)<dH$ throughout. Consequently a genuine smaller prime in that interval has just this one sharp search direction. The exact maximal terminal stretches of whole blocks on both full-size examples are also kernel-checked. The guarantee describes what to test if a prime is in that range. [Universal width and exact control counts](../PrimeFactors/OffsetCoordinateMultiplicity.lean)

| Input and requested stretch | Blocks covered | Reductions | Gauss iterations | Offset positions tested | Outcome |
| --- | ---: | ---: | ---: | ---: | --- |
| 49-bit product, full interval, original block loop | 2,884 | 2,884 | 12,897 | 1,831 | Both primes recovered |
| Same product and full interval, combined blocks | 2,884 | 914 | 4,265 | 1,831 | Same two primes |
| Fresh 2,048-bit product, first four blocks, combined | 4 | 1 | 109 | 3 | Full cofactor remains |
| Same product, last $2^{257}$ blocks, combined | $2^{257}$ | 1 | 3 | 3 | Full cofactor remains |

The terminal run starts a public distance from $\lfloor\sqrt N\rfloor$. It used three guide tests and one guide-interval square root. The only remaining direction in this stretch was $(1,1)$, whose trace equals $p+q$ if a factor lies there. Across the full row, more than $2^{509}$ offset positions still pass the residue and band filters after the three checks. This row count also includes offsets outside the terminal factor interval. The earlier blocks remain unresolved. Roughly one part in $10^{76}$ of the fresh input's blocks was covered by this run. The reproducible comparison measures saved work in choosing coordinate pairs. [Complete small comparison](https://marius-bughiu.github.io/prime-factors/#offset-factor-blocks-coalesced-49) · [Full-size prefix](https://marius-bughiu.github.io/prime-factors/#offset-factor-blocks-coalesced-fresh-prefix-2048) · [Full-size terminal interval](https://marius-bughiu.github.io/prime-factors/#offset-factor-blocks-coalesced-fresh-tail-2048)

## How much information would identify a block?

Allow the middle coefficient $t$ to vary in the related form $F_t(x,y)=px^2-txy+qy^2$. Everything below the bound $U=\lfloor\sqrt{2N}\rfloor$ is a public query location. Balance gives $q\le U\le2p$. On the entire interval $0\le t\le U$, Lean proves

$$\min_{(x,y)\ne(0,0)}F_t(x,y)=\min(p,p+q-t).$$

Indeed $2F_t=(2p-t)x^2+(2q-t)y^2+t(x-y)^2$. The three coefficients are nonnegative and at least two of the integer squares are positive. The two formula values are attained at $(1,0)$ and $(1,1)$. Thus the axis is shortest exactly when $t\le q$, and the diagonal is shortest exactly when $q\le t$. They tie at the larger factor. At $N=2501=41\times61$, the two vectors have values $(41,42)$ at $t=60$, $(41,41)$ at $61$, and $(41,40)$ at $62$. The diagonal is always a valid answer at the public endpoint $U$ for any balanced pair. Computing which direction wins at a chosen intermediate $t$ requires information about the hidden coefficients. [Minimum, threshold and endpoint proofs](../PrimeFactors/OffsetMinimumThreshold.lean)

The exact threshold also tells us how accurate a proposed predictor would have to be. Suppose a procedure using only $N,t$ returns one of these two directions and guarantees its value is within $e$ of the true minimum at every queried $t$. An axis answer implies $q\ge t-e$. A diagonal answer implies $q\le t+e$. Starting from the public larger-factor range and querying the midpoint each time, an initial width of at most $2e+2^kB$ falls to at most $2e+B$ after $k$ queries. Adversarial choices in the overlap are allowed. For 1,024-bit factors and $e=2^{508}$, **514 such answers** suffice to put $q$ in an interval of width $2^{510}$. If $[l,h]$ is that interval with $l\ge\sqrt N$, then $p$ is in $[\lceil N/h\rceil,\lfloor N/l\rfloor]$. Its width is at most $h-l$ because $N/(lh)\le1$. This would supply an interval for the three-coordinate theorem. Finding a product-only predictor with that guarantee remains open. Known high bits at a comparable scale already have a classical factor-recovery application. [Error bounds and checked bisection](../PrimeFactors/OffsetMinimumThreshold.lean) · [Coppersmith on factoring with known high bits](https://doi.org/10.1007/s001459900030)

A simple candidate predictor uses the midpoint of the public range for $q$ as its fixed switching point. With equal prime bit width $b$, this midpoint is $m=\lfloor(\lfloor\sqrt N\rfloor+1+\min(U,2^b-1))/2\rfloor$. Its largest additive error over the public range, allowing the query at the midpoint to go either way, is within one of $|q-m|$. The latter has 1,020 bits on the fresh control and 1,019 bits on the crossed control. Both miss the required precision by hundreds of bits. The product determines the midpoint. The already published primes are used only to check its error. [Control inputs and prime witnesses](../experiments/offset_winner_positions.py)

```sh
python3 -m experiments.offset_factor_blocks 129133 --block 262 269
python3 -m experiments.offset_factor_blocks 122821 --block 256 258
python3 -m experiments.offset_factor_blocks 502005281288939 --max-blocks 10000 --max-tests 500000
```
