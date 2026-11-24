# How often can two fractions from one draw reveal a factor?

Subsequent work studies what happens when the source can be chosen from every digit of the product. It gives an input-population bound and exhibits two 2,048-bit products whose smallest working fractions differ by more than 2,000 bits in height. [Choosing a short fraction](choosing-a-short-fraction.md)

Let $N=pq$ be a 2,048-bit integer with distinct 1,024-bit primes $p<q$. For one unit residue $r$ modulo $N$, consider **all** reduced fractions $a/b$ with $b>0$, $a\equiv br\pmod N$, and $0<2|a|b<N$. The event is that two distinct fractions have signed norms $ab,cd$ whose product is an integer square. Such a pair always splits $N$. The bounds allow prime factors of any size in all four entries.

| How $r$ is drawn | One draw | At least one pair in $2^{48}$ draws |
|---|---:|---:|
| $r$ uniform among the units | $<2^{-798}$ | $<2^{-750}$ |
| $r=x^2$ for a uniformly drawn unit $x$ | $<2^{-796}$ | $<2^{-748}$ |

These are unconditional bounds for every eligible $N$. Choosing the two fractions after inspecting the whole chain is allowed. The event concerns exactly two distinct rows from one source. A square formed from three or more rows, or from several sources, can satisfy different constraints. For the small example $N=437$, direct enumeration finds suitable pairs at 58 of its 396 unit residues. Exactly 64 of the 396 choices of $x$ give a suitable pair at $r=x^2$. [Example recovering 19 and 23](shared-root-signs.md#a-factor-from-two-rows-of-the-same-draw) · [Reproduce both counts and the 2,048-bit bound](../experiments/same_source_pair_bound.py)

## Why every such pair splits the product

The numerators must have the same sign. Order the two fractions so that $U=|a|d$ exceeds $V=|c|b$; equality would give identical reduced fractions. We have $U\equiv V\pmod N$, and $UV=abcd$ is square. With $g=\gcd(U,V)$, unique factorization gives $U=gu^2$, $V=gv^2$ with $u>v>0$ coprime. Every entry is a unit modulo $N$ since the fractions are reduced and represent a unit. The two height bounds imply $2guv<N$.

Thus $z=u/v\bmod N$ is a square root of 1. Since $0<u-v<u+v\le2uv<N$, neither $u-v$ nor $u+v$ is a multiple of $N$. The local signs of $z$ at $p,q$ must therefore differ. In particular $q$ divides one of $u-v,u+v$, so $u>q/2$. To actually find a prime, use $X=rbd$ and $Y=\sqrt{abcd}=guv$. Their ratio modulo $N$ is $\pm z$, and $\gcd(X-Y,N)$ gives $p$ or $q$. The calculation uses only $r$ and the two fractions. [Lean proof for the cross products](../PrimeFactors/SameSourcePair.lean)

## Counting the residues

Set $m=\gcd(|a|,|c|)$, $n=\gcd(b,d)$ and write $(|a|,|c|,b,d)=(mA,mC,nB,nD)$. Then $AD$ is coprime to $CB$. Indeed, the four possible overlaps are excluded by $\gcd(A,C)=\gcd(B,D)=1$ and by the original reduced fractions. Hence $g=mn$, $AD=u^2$, and $CB=v^2$. For fixed $(u,v)$ there are at most $\tau(u^2)\tau(v^2)=\tau((uv)^2)$ assignments of $A,D,C,B$, where $\tau$ counts divisors. The number of choices of $m,n$ with $mn\le G=N/(2uv)$ is at most $G(1+\ln G)$ by summing $\lfloor G/m\rfloor$. Here $G<p$. Each assignment and common numerator sign specify at most one $r$.

There are two possible mixed roots $z$ modulo $N$. For each, put $k=(zv-u)/N$, taking $1\le z<N$. Then $k/v$ is reduced and $|z/N-k/v|=u/(Nv)<1/(2v^2)$. Legendre's criterion places $k/v$ among the convergents of $z/N$. Each such convergent specifies a single positive $u$, and consecutive denominators satisfy $v_{j+2}\ge2v_j$. Counting both roots, including any repeated initial denominator 1, gives

$$
\sum_{(u,v)} (uv)^{-t}\le (q/2)^{-t}\frac4{1-2^{-t}}\qquad(t>0).
$$

This uses the mixed roots only to count possible witnesses. It does not require computing them. [Continued-fraction criterion and endpoints](shared-root-signs.md#enumerating-the-fractions-on-one-euclidean-chain)

## A finite divisor bound

Take $\delta=171/1024$, $t=1-\delta$, and set

$$
C=\prod_{\ell\ \mathrm{prime}}\max_{e\ge0}(2e+1)\ell^{-\delta e}.
$$

Then $\tau(w^2)\le Cw^\delta$ for every positive $w$. Successive terms in each maximum have decreasing ratio $(2e+3)/[(2e+1)\ell^\delta]$. Only the primes with $\ell^\delta<3$ can enlarge $C$. The certificate finds 128 such primes and computes $C^{1024}$ exactly as a rational number.

Dividing the count by $\varphi(N)$ gives a bound for uniform $r$. For uniform $x$, each qualifying $r$ has at most four square roots. Combining the two sign choices, the estimate for $G$, and the convergent sum yields

$$
P_{x^2}\le 16\frac{N}{\varphi(N)}\,(1+\ln p)\,\frac{C}{1-2^{-t}}\,(q/2)^{-t}.
$$

The bound for uniform $r$ is one quarter of this expression. Since $q\ge\sqrt N\ge2^{1023.5}$, we have $q/2\ge 2^{1022.5}$. Also $N/\varphi(N)<101/100$, $1+\ln p<718$, and $1/(1-2^{-t})<5/2$. The integer certificate raises the resulting inequality to power $2048$ and verifies $P_{x^2}<2^{-796}$. A union bound supplies the batch column in the table. [Standalone certificate](../experiments/same_source_pair_bound.py)

## Finding the pair from the product alone

For 437, the fractions $9/1$ and $4/49$ both represent 9 modulo 437, because $9\cdot49=441=437+4$. Their norms multiply to $9\cdot196=42^2$. The gcd of $441-42=399$ and $437$ is 19, giving $437=19\cdot23$. The Lean theorem checks this calculation and proves that the gcd gives a proper divisor for every pair satisfying the stated hypotheses. The frequency estimate above uses a separate counting argument and an exact integer certificate. [Lean theorem and example](../PrimeFactors/SameSourcePair.lean)

The search walks the continued fractions for each public residue. It groups the signed norms by their sign and two observations at each of the 15 odd primes through 53. At a prime $\ell$, remove all powers of $\ell$ from the norm's magnitude, record the parity of the exponent removed, and record whether the remainder is a square modulo $\ell$. Two norms whose product is a positive square must agree on every observation. Lean proves this for every prime. Each surviving comparison gets an exact test using a gcd and two integer square roots. This avoids factoring a norm and also handles a test prime that divides just one norm to an even exponent. A sampled nonunit or a nonprimitive Euclidean row can independently give a factor by gcd. The probabilities in the table concern the specified fraction-pair event. [Search](../experiments/pair_class_search.py) · [Lean proof of the filter](../PrimeFactors/SquareClassFilter.lean)

On the established 2,048-bit control, 256 reproducible draws in each mode gave the following counts. The two modes shared the same starting integers. Each mode finished with the entire input unresolved. On the smaller input 77,837, the unit search found 277 and 281 on draw 17. Its two fractions were $31/20$ and $1/12555$. [Benchmark inputs, budgets and expected outcomes](../benchmarks/same-source-pairs.json)

| Residue used for the search | Short fractions | Pairs before filtering | Exact pair tests | Factors found |
|---|---:|---:|---:|---:|
| Sampled unit | 221,025 | 95,354,689 | 38 | 0 |
| Square of sampled unit | 220,779 | 95,148,814 | 55 | 0 |

We also enumerated every eligible fraction directly for every square unit residue on all 111 products of distinct odd primes of equal bit length through 127. The Euclidean search returned the same fractions. Among 2,748,472 pairs, exactly 4,740 had square product, across 4,446 residues. Every one revealed both primes. Longer combinations behave differently. For example, modulo 437 the residue 282 gives a minimal four-row square whose gcd fails on all four possible starting roots. Run `python3 -m experiments.same_source_pairs --prime-limit 127 --extended` to repeat this census. [Independent enumeration](../experiments/same_source_pairs.py) · [Small regression examples](../tests/test_same_source_pairs.py)

Across $2^{48}$ independent uniform unit draws used as square sources, a two-row exact square can either use one source twice or two different sources once each. The former has probability below $2^{-748}$ by the count above. The latter is included in the earlier $2^{-46}$ bound on dependencies using a source once. Their sum is below $2^{-45}$. A remaining possibility is a combination of three or more rows in which every participating source supplies at least two rows. [Bound for combinations with a singly used source](smooth-fraction-budget.md#when-primes-can-cancel-between-different-draws)
