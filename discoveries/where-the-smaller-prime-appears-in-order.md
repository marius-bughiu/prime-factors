# Where does the smaller prime appear in an ascending scan?

For two uniformly chosen distinct 1,024-bit primes whose product has 2,048 bits, **testing feasible odd candidates from smallest to largest reaches the smaller prime before 48.5% of the interval on average**. Searching backwards takes more than 51.5% on average, and a uniformly shuffled order takes at least 50%. Each product contributes its own one-based hit position divided by its own candidate count. The bound covers the whole eligible population, including products very near the upper endpoint. It ranks trial divisions. Those intervals are still far too large to scan on a personal computer. [Finite inequalities and integrals](../PrimeFactors/AscendingDivisorRank.lean) · [Earlier comparison within specified product bins](which-half-contains-the-smaller-prime.md)

Let $B=2^{1023}$ and sort the primes as $p<q$. For the public product $N=pq$, set $L=\lceil N/(2B-1)\rceil$ and $U=\lfloor\sqrt N\rfloor$. The eligible range of products ensures $L\ge B$. Write $C(t)=\lfloor(t+1)/2\rfloor-\lfloor L/2\rfloor$. The quantity being averaged is $C(p)/C(U)$. The search can compute both endpoints from $N$ and the known bit widths. Counting includes the test of $p$ itself.

## The continuous rank and its bias

Normalize the product as $x=N/B^2$ and put $a=\log(2/\sqrt x)$. In continuous factor coordinates the lower endpoint is $l=N/(2B)$ and the upper endpoint is $s=\sqrt N$. At fixed $x$ write $v=\log(p/l)$. Then $0\le v\le a$, $2\le x<4$, and the area element in the $(p,q)$ plane is $B^2\,dx\,dv$. Indeed $p=Bx e^v/2$ and $q=2Be^{-v}$. The normalized ordinal $R=(p-l)/(s-l)$ is $(e^v-1)/(e^a-1)$. Integrating in $v$ gives the conditional area mean $1/a-1/(e^a-1)$. Lean proves this is at most $1/2-a/13$ throughout the required range, using a four-term Taylor bound on $e^a$. [Fiber integral and inequality](../PrimeFactors/AscendingDivisorRank.lean)

Integration over the entire product range gives
$$
P_0=\int_2^4a\,dx=1-\log2,\qquad
J_0=\int_2^4 a^2\,dx=1-\log2-\tfrac12(\log2)^2>0.217P_0 .
$$
Thus the integral of $R$ in units of $B^2$ is at most $P_0/2-J_0/13$. The smooth prime density $1/(\log p\log q)$ lies between $1/710^2$ and $1/709^2$. The smooth population mass in those units is at least $P_0/710^2$, and its rank total is at most $(P_0/2-J_0/13)/709^2$. [Integrated moments and numerical comparison](../PrimeFactors/AscendingDivisorRank.lean)

## Passing to actual odd primes

For every interval of $[B,2B]$, partial summation of Axler's unconditional estimate bounds the error between its prime count and $\int dt/\log t$ by $\epsilon=4\cdot10^{-13}B$, including either choice of endpoints. To use this for a weighted rank, fix $0\le t\le1$ and count the pairs for which $R\ge t$. In normalized factors $z=p/B$, $y=q/B$, this condition is
$$
 (1-t)y/2+t\sqrt{y/z}\le1 .
$$
Its left side increases in $y$ and decreases in $z$. Slicing in either direction, intersecting with $1\le z<y<2$ and $zy\ge2$ still gives an interval. Replacing each prime-count measure in turn therefore changes the count by at most $\epsilon(2B/709+\epsilon)<1.2\cdot10^{-15}B^2$. This applies to the whole eligible region as well. Integrating the bound from $t=0$ to 1 bounds the error on the rank total because $R=\int_0^1\mathbf1_{R\ge t}\,dt$. [Axler, Proposition 1.1](https://arxiv.org/pdf/2203.05917#page=1) · [Explicit interval-error derivation](what-the-square-root-reveals-about-the-gap.md#removing-the-rh-assumption-from-the-decision)

Finally $l\le L<l+2$. With $D=s-l$, $k=C(p)$ and $w=C(U)$, parity and rounding give $2k\le DR+2$ and $2w\ge D-3$. If $D\ge1{,}000{,}003$ the normalized hit rank exceeds $R$ by at most $5\cdot10^{-6}$. Otherwise $2B-p\le3D$, so both primes lie in the last 3,000,009 integer positions. Fewer than $(3{,}000{,}010)^2$ such pairs are possible among over $2^{2021}$ eligible pairs. Allowing a full unit of rounding error on every exceptional pair increases the overall mean by less than $6\cdot10^{-6}$ including the ordinary rounding error. Combining the count and rank bounds yields the stated 48.5%. Reverse order changes $k$ to $w+1-k$. Every rank is equally likely under a uniform shuffle. [Eligible population lower bound](../PrimeFactors/ChebyshevPrimeSample.lean) · [Rounding and final comparison](../PrimeFactors/AscendingDivisorRank.lean)

Lean checks the fixed-product integral, its upper bound, the integrated log-width moments, monotonicity, integer-rounding inequalities the bound for the exceptional set, and the finite population aggregation in `finite_mean`. Its hypotheses explicitly record the smooth mass, the integrated count discrepancy and the per-pair rounding allowance. The Jacobian calculation, use of the published prime-count estimate on interval sections, and integration of their errors are the written steps connecting the actual population to that implication.

As a check on the statistic, complete enumeration of all eligible pairs at smaller widths gave the following results. Each percentage is an arithmetic mean of individually normalized one-based positions. The analytic 48.5% bound above uses 1,024-bit factors.

| Bits per prime | Eligible pairs | Ascending | Descending | Uniform shuffle |
|---:|---:|---:|---:|---:|
| 10 | 1,718 | 45.838% | 55.882% | 50.860% |
| 12 | 19,546 | 47.619% | 52.789% | 50.204% |
| 14 | 228,713 | 48.207% | 51.893% | 50.050% |
| 16 | 2,753,877 | 48.609% | 51.416% | 50.012% |

The following Python reproduces a row using just its prime width. The divisions defining the ranks and candidate counts use integers. Floating point is used only for the displayed census means.

```python
from itertools import combinations
from math import isqrt

def census(bits):
    B = 2**(bits-1)
    primes = [p for p in range(B, 2*B) if
              all(p % d for d in range(2, isqrt(p)+1))]
    pairs = 0
    ascending = descending = shuffled = 0.0
    for p, q in combinations(primes, 2):
        n = p*q
        if n < 2*B*B:
            continue
        lower = (n+2*B-2)//(2*B-1)
        width = (isqrt(n)+1)//2 - lower//2
        rank = (p+1)//2 - lower//2
        pairs += 1
        ascending += rank/width
        descending += (width+1-rank)/width
        shuffled += (width+1)/(2*width)
    return pairs, ascending/pairs, descending/pairs, shuffled/pairs
```
