# Reading a factor from one missing term

If someone could supply 1,024 particular measurements of a 2048-bit product, we could read off its smaller prime, one binary digit per measurement. Lean verifies this even when every complex measurement has absolute error just under one half. We know how to decode the measurements. Computing them cheaply from the product is the open question. [Lean decoder and error bound](../PrimeFactors/TruncatedRamanujan.lean)

## What a measurement contains

Let $N=pq$ for two distinct 1024-bit primes with $p<q$, and put $L=\lfloor\sqrt N\rfloor$. Among the numbers from 1 through $L$, exactly one shares a prime factor with $N$. It is $p$, since $p\le L<q$ and $L<2p$. Give each position $x$ a complex weight $z_x=e^{2\pi i kx/N}$ at a public integer frequency $k$. The measurement is the difference

$$
R(k)=\sum_{x=1}^L z_x-\sum_{\substack{1\le x\le L\\\gcd(x,N)=1}}z_x=z_p.
$$

The first sum is a geometric series. The second is a truncated version of the classical Ramanujan sum. For these equal-width primes the **complete** Ramanujan sum equals 1 at every frequency the decoder requests. Truncating at $L$ leaves a single term carrying the position of $p$. [Ramanujan’s original definition, §1](https://ramanujan.sirinudi.org/Volumes/published/ram21.pdf) · [Complete transform](../PrimeFactors/FourierAccess.lean)

The frequencies are fixed by $N$ alone. At digit $j$, put $w=2^j$, use $k=\lfloor N/(2w)\rfloor$, and rotate the reading by $-2\pi r/(2w)$, where $r$ is the value of the low digits recovered so far. The sign of the real part gives the next digit. Rounding the frequency down shifts the phase by less than $1/q$ of a turn, leaving a real-part margin of at least $1/2$. The error allowance applies to the unnormalized difference above. If an evaluator divides the sums by $L$, the allowed absolute error becomes $1/(2L)$.

## A small numerical check

For $N=15049$ the following Python example computes the truncated sum directly. On each of its seven readings it subtracts 0.499 from the magnitude of the real part after rotation, pushing the decision toward the wrong sign. It recovers 101, and $15049/101=149$. The smallest real-part magnitude before perturbation was about 0.999711. These are floating-point observations. The margin for all eligible inputs is the separate Lean theorem. [Bit-reading theorem](../PrimeFactors/TruncatedRamanujan.lean)

```python
from cmath import exp
from math import copysign, gcd, isqrt, pi

n, r = 15049, 0
length = isqrt(n)
for j in range(length.bit_length()):
    w = 2**j
    k = n // (2*w)
    z = [exp(2j*pi*((k*x) % n)/n) for x in range(1, length+1)]
    reading = sum(z) - sum(v for x, v in enumerate(z, 1) if gcd(x, n) == 1)
    real = (reading * exp(-2j*pi*r/(2*w))).real
    if real - copysign(0.499, real) < 0:
        r += w
print(r, n // r)  # 101 149
```

For a full-size input, directly scanning the $L$ summands already encounters the factor by gcd. Independent uniform sampling also struggles. Only one position contributes to the difference, and $L\ge2^{1023}$. Lean shows that even $2^{40}$ such samples have probability at most $2^{-983}$ of touching that position. A practical use of this identity needs an evaluator that exploits the arithmetic structure of the whole truncated sum. No RH assumption enters the identity or the sampling bound. [Exact sampling calculation](../PrimeFactors/TruncatedRamanujan.lean)
