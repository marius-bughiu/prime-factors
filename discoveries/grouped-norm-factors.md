# One square test for several possible factor ratios

For an explicit family of products, the product itself selects a single square test that recovers both factors. On 50,629 it selects $k=56$ and returns **257 × 197**. The test also groups several possible factor ratios when the right $k$ is supplied. A single fixed choice recovered primes on two different products, and a complete search found no applicable choice on either standard 2,048-bit control. [Lean proofs, checked primes and control exclusions](../PrimeFactors/GroupedNormFactors.lean) · [How many products satisfy the condition?](grouped-norm-frequency.md)

## The product-only test

Compute $T=\lfloor\sqrt N\rfloor$ and $h=N-T^2$. For a positive integer $k$ with $h>0$ and $hk<T$, test whether

$$
1+4k(T-hk)=(2m+1)^2.
$$

An exact square gives $m(m+1)=k(T-hk)$. Then $A=kT-m$ and $B=kT+m+1$ have product $k^2N$. Both are positive and below $N$. Indeed $k<T$, $m<T$ and $B\le(T-1)T+T=T^2$. Thus $\gcd(A,N)$ is a proper divisor. The test examines precisely the first possible weighted factor sum whenever it succeeds, since $4k^2N$ lies strictly above $(2kT)^2$ and at most $(2kT+1)^2$. Applying Fermat's difference of squares to multiples of $N$ is the classical Lawrence–Lehman method. [Hittmeir, Section 4](https://arxiv.org/pdf/2006.16729#page=5)

The accepted square also reconstructs both factors directly. Let $b=\gcd(k,m)$, $a=k/b$, $u=m/b$ and $v=(m+1)/a$. The last division is exact because $k\mid m(m+1)$ and $a$ is coprime to $u$. Then $av-bu=1$, $T=uv+hab$ and

$$
N=(u^2+h a^2)(v^2+h b^2).
$$

Conversely, for positive $a,b,u,v,h$ with $av-bu=1$, these two factors have product $(uv+hab)^2+h$ and weighted sum $b^2p+a^2q=2ab(uv+hab)+1$. Since $h≤T=uv+hab$, this $T$ is the integer square root of $N$. Testing $k=ab$ recovers a factorization. Swapping the two sides treats determinant $-1$ as well. The endpoint $T=hk$ gives the immediately visible factorization $h(hk^2+1)$, which is proper for $h>1$. An exact square $N=T^2$ is already factored as $T\cdot T$. [Executable test and converse](../PrimeFactors/GroupedNormFactors.lean)

## When the product chooses the multiplier

Test the largest possible multiplier first, $k_0=\lfloor(T-1)/h\rfloor$. Its distance from the correct one on this family is exactly

$$
k_0-ab=\left\lfloor\frac{uv-1}{h}\right\rfloor.
$$

If $uv\le h$, the first test is guaranteed to return two proper factors, regardless of the size of $ab$. More generally, $uv\le Jh$ guarantees a hit within the first $J$ descending tests. The hypothesis describes the factors. Computing $k_0$, testing the square and checking the recovered product use only $N$. [Lean selection and recovery theorems](../PrimeFactors/GroupedNormFactors.lean)

For $N=50{,}629$, we obtain $T=225$, $h=4$, and $k_0=56$. The discriminant is $225=15^2$, so $m=7$ and $b=\gcd(56,7)=7$. The resulting $a=8$, $u=v=1$ give primes $1+4\cdot8^2=257$ and $1+4\cdot7^2=197$. Lean verifies the one-probe output and both primality claims. [Checked example](../PrimeFactors/GroupedNormFactors.lean)

## How many ratios can share one test?

Fix any coprime $a,b>0$. From one integer solution $av_0-bu_0=1$, set $u=u_0+at$ and $v=v_0+bt$. For all sufficiently large $t$ the factors are positive and their ratio $p/q$ tends to $(a/b)^2$. Thus each coprime split of a single $k$ gives a different possible limiting ratio, all served by that same test. This construction establishes integer families. Whether each family contains infinitely many simultaneous prime pairs remains open.

For example, $k=2\cdot3\cdot5\cdots43=13{,}082{,}761{,}331{,}670{,}030$ has **213** splits $k=ab$ with $a<b$ and $b^2<2a^2$. Each gives a limiting ratio strictly within the balanced interval. The following count uses only the explicit primes and does not enter the factor search.

```python
from math import prod

primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
k = prod(primes)
divisors = [1]
for p in primes:
    divisors += [p * a for a in divisors]
assert sum(a < k // a and (k // a)**2 < 2*a*a for a in divisors) == 213
```

## Examples and coverage

To obtain the two examples, we fixed $k=30{,}030$ and visited even $T\ge 2k$ in order with $N=T^2+1$. We kept the first balanced pair of distinct primes for each recovered coefficient split. The search selected examples from this special family. Lean verifies both outputs, their primality and the decoder's product identity. [Checked examples](../PrimeFactors/GroupedNormFactors.lean)

| Public product | $T$ | Square root $2m+1$ | Recovered prime factors |
|---:|---:|---:|---:|
| 656,618,502,401 | 810,320 | 306,151 | 639,941 × 1,026,061 |
| 65,915,335,618,277 | 8,118,826 | 985,711 | 8,955,293 × 7,360,489 |

A fixed $k$ takes one square test after computing the public window and a gcd on success. Searching all eligible $k$ requires up to $\lfloor(T-1)/h\rfloor$ tests. For the fresh and crossed 2,048-bit products, $T/2<h<T$ leaves only $k=1$, and its square test fails on both. The proof uses only the public products and bounds the target strictly between consecutive values of $m(m+1)$. [Full-size control theorem](../PrimeFactors/GroupedNormFactors.lean)
