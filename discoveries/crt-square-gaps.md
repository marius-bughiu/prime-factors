# What a square quotient tells us about the prime gap

For $667=23\cdot29$, the midpoint 26 satisfies $26^2-667=9$. Dividing by $3^2$ gives the square 1. Subtracting and adding 3 to 26 recovers 23 and 29. Changing the divisor from 3 to 5 makes this kind of direct split impossible, even if the search can try every midpoint. The reason is that the distance from 26 to either factor is 3, and 5 does not divide it.

## An exact criterion for one row

Let $N=pq$ with distinct odd primes $p<q$, let $D>0$, and set $g=(q-p)/2$. A positive square quotient $s^2$ gives

$$t^2=N+(Ds)^2,\qquad (t-Ds)(t+Ds)=N.$$

If $t-Ds>1$, the two positive factors must be $p$ and $q$ in that order. Consequently $t=(p+q)/2$ and $Ds=g$. Conversely, if $D\mid g$, taking precisely that midpoint and $s=g/D$ gives the split. For a cutoff $s^2\le Y$, the exact conditions are $D\mid g$ and $(g/D)^2\le Y$. The cutoff-free result already limits every search that depends on a single positive square quotient. Several nonsquare or negative quotients may have a square product and yield a separate split. [Lean characterization](../PrimeFactors/CRTSquareNorm.lean)

## If any 32 primes through 739 can be selected

Take the uniform population of distinct 1,024-bit primes whose product has 2,048 bits. Put $X=2^{1023}$, $U=X/\log X$, and $\mathcal L=\{3,5,\ldots,739\}\cap\mathbb P$. There are 130 primes in $\mathcal L$. Let $D$ be a product of any 32 of them. Its selection can depend on every digit of $N$. On fewer than $2^{-112}$ of these inputs can **any** such selection produce the direct square split. An interval bound on primes improves this to $2^{-117}$. These are necessary divisibility conditions even with unrestricted computation and an unlimited quotient cutoff.

For fixed $p$ and $D$, the condition $D\mid g$ means $q\equiv p\pmod{2D}$. There are at most $X/(2D)+1$ integers from this class in $[X,2X)$. Write $S=e_{32}(1/\ell:\ell\in\mathcal L)$ for the sum of $1/D$ over all subsets, and $K=\binom{130}{32}$. Summing over selections bounds the eligible partners by $XS/2+K$. There are fewer than $1.511U$ choices of $p$ and more than $(0.22U)^2$ eligible ordered pairs. With $\log X<710$, the resulting bound is

$$\frac{1.511\cdot710}{0.22^2}\left(\frac{S}{2}+\frac{K}{X}\right)<2^{-112}.$$

For the exact arithmetic check let $M=\prod_{\ell\in\mathcal L}\ell$. The coefficient of $z^{32}$ in $\prod(\ell+z)$ equals $MS$ and is computable using only integer additions and multiplications. [Finite Lean check](../PrimeFactors/CRTSquareNorm.lean) · [Prime-pair population bounds](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)

The Brun–Titchmarsh interval inequality gives at most $2X/(\varphi(D)\log(X/D))$ prime partners by using the class modulo $D$. Here $D<2^{298}$, as seen by multiplying the largest 32 primes on the list. Replacing $S$ by $e_{32}(1/(\ell-1))$ accounts for the totients. The bound is $(2\cdot1.511/0.22^2)(1023/725)e_{32}(1/(\ell-1))<2^{-117}$. [Montgomery and Vaughan, Theorem 2](https://doi.org/10.1112/S0025579300004708)

## If the first 32 splitting primes are selected

The implemented rule goes through the odd primes in order and takes the first 32 for which $N$ is a nonzero square. Fix $p$. At a prime $\ell\in\mathcal L$ all possible prime partners $q$ are units. Exactly $(\ell-1)/2$ unit residues have Legendre symbol opposite to that of $p$ and let the search skip $\ell$. Among the residues that make $N$ a square, exactly one, $q\equiv p\pmod\ell$, lets a direct split eventually succeed. Selecting any other residue at a splitting prime prevents success.

Start with one residue class that has selected zero primes. For each $\ell$ update the counts $c_k$ for $0\le k<32$ and the count $b$ that has already reached 32. The Chinese remainder theorem gives

$$c'_k=\tfrac{\ell-1}{2}c_k+c_{k-1},\qquad b'=(\ell-1)b+c_{31},\qquad c_{-1}=0.$$

After processing 739, each of the $b$ finished classes modulo $M$ contains at most $X/M+1$ partners. Across the population this gives a bound below $2^{-147}$ for direct success with the 32nd prime at most 739. If the 32nd prime occurs later, the pair must belong to one of the $\sum c_k$ still-surviving classes. Including every such class gives a bound below $2^{-113}$ for eventual direct success **with no cutoff on the last prime**. These results count exact CRT classes and require no assumption about random Legendre symbols across the observed products. [Finite Lean comparisons](../PrimeFactors/CRTSquareNorm.lean)

For the cutoff at 739, Brun–Titchmarsh also gives $2^{-152}$. Index the listed primes in order as $\ell_j$, put $M_j=\prod_{i\le j}\ell_i$, and $b_j^*=c_{31}$ immediately before processing $\ell_j$. There are $b_j^*$ successful unit classes first finishing at this prime. The bound is

$$\frac{2\cdot1.511}{0.22^2}\sum_j \frac{b_j^*}{\varphi(M_j)}\frac{1023}{1023-\operatorname{bitlength}(M_j)}<2^{-152}.$$

Here $M$ has 1,018 bits, so all denominators are positive and the logarithm in the prime-count inequality is bounded away from zero. The following exact rational computation reproduces both bounds that use Brun–Titchmarsh. Lean checks the three integer-count bounds and the square-quotient equivalence. The interval estimates for primes enter on paper.

```python
from fractions import Fraction as F
from math import isqrt, prod

primes = [p for p in range(3, 740, 2)
          if all(p % d for d in range(2, isqrt(p) + 1))]
assert prod(primes[-32:]) < 2**298
coeff = [F(1)] + [F(0)] * 32
running = [1] + [0] * 31
modulus = phi = 1
mass = F(0)
for p in primes:
    for k in range(32, 0, -1):
        coeff[k] += coeff[k-1] / (p-1)
    modulus *= p
    phi *= p-1
    mass += F(running[-1], phi) * F(1023, 1023-modulus.bit_length())
    running = [(p-1)//2 * now + prev
               for now, prev in zip(running, [0] + running)]
scale = F(2*1511*10_000, 1000*22**2)
assert scale * F(1023, 725) * coeff[32] < F(1, 2**117)
assert scale * mass < F(1, 2**152)
```
