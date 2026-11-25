# A factorization first visible at offset 13

On **2,376,225,323**, the thirteenth public offset found **36,559 × 64,997**. Lean proves that each of the preceding twelve offsets either has no eligible multiplier or fails its square test. The same result holds throughout an infinite family of integer products whose factor ratio tends to $16/9$. How often this family contains two primes is open. Across 128 independently generated products of two 24-bit primes, offsets 1 through 32 found no factor. [Lean family and prime certificates](../PrimeFactors/GroupedNormOffsets.lean) · [Reproducible experiments](../experiments/grouped_offset_sweep.py)

## What each offset tests

Given $N$, set $T=\lfloor\sqrt N\rfloor$ and $h=N-T^2$. For each positive offset $j$ and $h>0$, let $k=\lfloor(jT-1)/h\rfloor$. Skip $k=0$. The residual $z=jT-hk$ satisfies $1\le z\le h$. Test whether

$$
D=j^2+4kz=(2m+j)^2.
$$

An integer square root necessarily has the indicated parity. On success, $m(m+j)=kz$ and $(kT-m)(kT+m+j)=k^2N$. If $j\le h$, the lower signed gcd $\gcd(kT-m,N)$ is guaranteed to be proper. To see the bounds, $hk<jT$ gives $k<T$, and $mj\le m(m+j)=kz\le kh<jT$ gives $m<T$. Thus both signed factors are positive and smaller than $N$. For other offsets the implementation tries both gcds and verifies any proper divisor it finds. This is a difference-of-squares test on the classical weighted multiple $4k^2N$. The new search rule derives both the multiplier and candidate sum from $N$ and $j$. [Proof](../PrimeFactors/GroupedNormOffsets.lean) · [Weighted Fermat method, Hittmeir, Section 4](https://arxiv.org/pdf/2006.16729#page=5)

Each accepted test has a specific integer structure. Put $b=\gcd(k,m)$, $a=k/b$, $u=m/b$ and $v=(m+j)/a$. The last division is exact because $a$ is coprime to $u$ and $a\mid u(m+j)$. Then $ab=k$, $av-bu=j$ and $uv=z$. In particular,

$$
(u^2+ha^2)(v^2+hb^2)=j^2N.
$$

Conversely, $av=bu+j$, $ab=k$ and $uv=z$ force a square hit via $m=bu$. The multiplier choice corresponds exactly to $0<uv\le h$ and $jT=uv+hab$.

When $g=\gcd(j,k)>1$, the offset $j/g$ selects $k/g$: its positive residual is $z/g\le h$. Its discriminant is $D/g^2$, so it passes exactly when $D$ passes. The signed factors also scale by $g$. If $g$ is coprime to $N$, the gcds stay the same and the larger square test can be skipped. A proper common divisor of $g$ and $N$ already splits the input. [Scaling and structural proofs](../PrimeFactors/GroupedNormOffsets.lean)

## Why the first twelve offsets fail

For $r\equiv58\pmod{77}$ define $N=(9r+1)(16r+5)$. Its public values are $T=12r+2$ and $h=13r+1$. At every $1\le j\le13$, the chosen multiplier is $k=j-1$, with residual $z=j+1+(13-j)r$. Thus offset 1 has no eligible multiplier. For each $2\le j\le12$, the computed $D=j^2+4(j-1)z$ has a nonsquare remainder modulo 7 or 11. Lean checks all possibilities modulo 77. At offset 13, $k=12$, $z=14$, $D=29^2$ and $m=8$. Since $12T-8=16(9r+1)$ and $16r+5$ is coprime to 16, its gcd with $N$ is exactly $9r+1$. The example above takes $r=4062$. The smaller example at $r=674$ gives $65,456,863=6,067\times10,789$. The proofs verify both displayed pairs of primes and the formula for all eligible $r$. [Formal exclusions and examples](../PrimeFactors/GroupedNormOffsets.lean)

## Independent results

The schedule always tested the largest eligible $k$ for each $j=1,\ldots,32$. The first two rows enumerate every distinct equal-width prime pair producing a full-width product. The three larger panels draw without reference to this method, using independent SHAKE-256 streams and rejecting repeated primes and undersized products. The search receives each product alone. The Fermat comparison tries the first 32 parity-eligible ordinary midpoints. The last column counts actual discriminant square tests across the complete offset schedule, including those after a factor was found. [Panel generator and accounting](../experiments/grouped_offset_sweep.py)

| Prime bits | Inputs | Offset 1 hits | Any offset through 32 | Ordinary Fermat hits | Both | Offset square tests |
|---:|---:|---:|---:|---:|---:|---:|
| 7 | 42 | 0 | 26 | 42 | 26 | 727 |
| 8 | 148 | 0 | 69 | 148 | 69 | 2,840 |
| 12 | 128 | 0 | 16 | 117 | 15 | 2,430 |
| 16 | 128 | 0 | 7 | 33 | 5 | 2,536 |
| 24 | 128 | 0 | 0 | 2 | 0 | 2,474 |

Across the three independent panels, three products split under an offset test and survived the 32 ordinary Fermat checks. Ordinary Fermat found more products overall. On the crossed and fresh 2,048-bit controls, respectively, duplicate removal left 22 and 20 square tests. Both complete schedules missed. The factor test at any fixed budget remains conditional on the input's arithmetic.

Run the comparison from the repository root with `python3 -m experiments.grouped_offset_sweep`.
