# Ruling out an offset before choosing its multiplier

On the fresh 2,048-bit input, small prime powers rule out **more than 77.82% of all offsets** through $U=\lfloor\sqrt{4h/3}\rfloor$, a 512-bit upper limit. On the crossed input they rule out **more than 82.76%**. Here $h$ is computed from the product alone. A rejected offset rules out **every primitive multiplier**, including multipliers beyond the usual positive-residual interval. This removes work from a complete offset schedule. Lean proves that on every product of two distinct 1,024-bit primes, at least one candidate in the sharp schedule passes every offset-divisor test and the executable probe returns one of the two prime factors. Hundreds of bits of offset search remain. [End-to-end theorem `complete_filtered_1024`](../PrimeFactors/OffsetDivisorSieve.lean) · [Public comparison products](../benchmarks/grouped-norm.json)

## A test that applies to the entire offset

Write $T=\lfloor\sqrt N\rfloor$, $h=N-T^2$, and choose integers $j>0,k$ with $\gcd(j,k)=1$. A successful signed test means that
$$
d^2=j^2+4k(Tj-hk).
$$
The two sides imply $d\equiv j\pmod2$, so $m=(d-j)/2$ is an integer. It satisfies
$$
m^2+hk^2=j(kT-m).
$$
Since $k$ is invertible modulo $j$, this forces $(m/k)^2\equiv-h\pmod j$, where the division means modular inversion. Thus a single obstructing prime power dividing $j$ rules out every such $k$. The proof covers even $j$ and negative $m$. For example, $N=91$, $j=38$, $k=35$ give $T=9$, $h=10$, $Tj-hk=-8$, $d=18$ and $m=-10$. The lower gcd recovers 13. Here $(-16)^2\equiv-10\pmod{38}$. [Theorems `signed_root` and `offset_divisor`](../PrimeFactors/OffsetDivisorSieve.lean)

Given any root, choose its representative $b$ with $2|b|\le j$. This is possible for every root, so this centering condition by itself removes no offsets. There is also a sharp limitation on rules that use only $h$ and $j$. If $-h$ has a square root modulo $j$, choose arbitrarily large positive lifts $b$ of that root and put $T=b+(b^2+h)/j$. Then $N=T^2+h$ has floor square root $T$ for all sufficiently large lifts, and $k=1$, $d=2b+j$ gives a square hit. The products in this converse are unrestricted nonsquares, and a given input supplies its own fixed $T$. The condition $m(m+j)\le h$ imposed by a top-multiplier search is a further restriction. [Theorems `centered` and `realizable_at_large_center`](../PrimeFactors/OffsetDivisorSieve.lean)

## How many offsets survive?

For each prime $p\le P$, take the smallest $p$-power $q$ at which $-h$ fails to be a square, if such a power exists. An offset survives this cutoff exactly when no listed $q$ divides it. For example, for the fresh input the list through $p=47$ is $4,5,11,13,17,19,23,31,37,81$. For the crossed input it is $4,5,7,9,11,17,19,23,37,47$. These lists include the first obstructing power at two and the exceptional powers at primes dividing $h$. Lean checks both lists on the actual products and proves that every multiple of every listed number fails for every primitive signed multiplier. [Full-size certificates](../PrimeFactors/OffsetDivisorSieve.lean) · [Prime-power calculation](../experiments/grouped_offset_rows.py) · [Square classes at odd primes and at two](counting-local-midpoints.md)

| Public input | Offsets in $1,\ldots,2^{40}$ surviving $p\le47$ | Surviving $p\le251$ | Fraction surviving $p\le10^6$ in $1,\ldots,U$ |
| --- | ---: | ---: | ---: |
| Fresh | 439,082,776,191 | 384,642,824,272 | 22.17237433% to 22.17237436% |
| Crossed | 371,111,694,749 | 295,636,324,676 | 17.23520981% to 17.23520983% |

The two integer columns count all distinct offsets by inclusion–exclusion. For pairwise coprime obstructions $Q=\{q_1,\ldots,q_s\}$ the count through $J$ is $\sum_{D\subseteq Q}(-1)^{|D|}\lfloor J/\prod_{q\in D}q\rfloor$. The first fresh count has 1,023 nonzero terms and the second has 847,257. The corresponding crossed counts have 1,024 and 4,879,229 terms.

The last column bounds the **finite** fraction over the full range. Set $\rho=\prod_q(1-1/q)$ and $\mu=\sum_q1/q$. Truncate the alternating divisor sums just after orders 17 and 18. The Bonferroni inequalities sandwich the empirical surviving fraction between the resulting sums of floors divided by $U$. The corresponding sums without flooring sandwich $\rho$, as seen by taking a uniform residue over the full product of the pairwise coprime $q$. Their difference is the order-18 elementary symmetric sum of the $1/q$, bounded by $\mu^{18}/18!$. Each floor introduces an error of less than $1/U$. The difference between the actual fraction and $\rho$ is therefore at most
$$
\frac{\mu^{18}}{18!}+\frac1U\sum_{i=1}^{18}\binom{s}{i}.
$$
The fresh input has 39,169 obstructions and the crossed input has 39,461. On both, $\mu<2$, $U\ge2^{511}$, and the binomial sum is below $2^{223}$. The error is below $4.1\cdot10^{-11}$ as a fraction. The interval argument and numerical bounds here are a paper calculation with reproducible integer checks. The signed necessity and its converse are kernel-checked. The percentages measure offsets removed before the multiplier search. Computational savings depend on how much work each surviving offset requires.

The following reproduces the counts and checks both displayed percentage intervals. It uses only the public product and integer arithmetic.

```python
import json
from math import comb, factorial, isqrt
from pathlib import Path
from experiments.grouped_offset_rows import local_failures
from scripts.factor import primes_through

def exact_count(limit, powers, start=0):
    total = limit
    for index in range(start, len(powers)):
        q = powers[index]
        if q > limit:
            break
        total -= exact_count(limit // q, powers, index + 1)
    return total

rows = json.loads(Path("benchmarks/grouped-norm.json").read_text())
bounds = {"grouped-norm-fresh-2048": (2217237433, 2217237436),
          "grouped-norm-crossed-2048": (1723520981, 1723520983)}
primes = primes_through(10**6)
for row in rows:
    if row["id"] not in bounds:
        continue
    n = int(row["n"])
    h = n - isqrt(n)**2
    U = isqrt(4*h // 3)
    for P in (47, 251, 10**6):
        bad, higher = local_failures(-h, [p for p in primes if p <= P], U)
        Q = sorted(bad + higher)
        if P < 10**6:
            print(row["id"], P, exact_count(2**40, Q))
            continue
        scale = 2**100
        lo = hi = scale
        mu = 0
        for q in Q:
            lo = lo*(q-1) // q
            hi = (hi*(q-1) + q-1) // q
            mu += (scale + q-1) // q
        count = sum(comb(len(Q), k) for k in range(1, 19))
        assert mu < 2*scale and U >= 2**511 and count < 2**223
        denom = factorial(18)*U
        err = 2**18*U + count*factorial(18)
        a, b = bounds[row["id"]]
        assert a*scale*denom < 10**10*(lo*denom - scale*err)
        assert 10**10*(hi*denom + scale*err) < b*scale*denom
```

For comparison with the existing top-multiplier experiment, at $J=2^{18}$ the full offset criterion leaves 47,004 fresh offsets and 35,142 crossed offsets. Among the primitive top choices already surviving the two selected coordinate tests, it reduces 12,878 to 3,554 on fresh and 11,430 to 2,219 on crossed. This bounded check recomputes the chosen bases for $J=2^{18}$. All exact square tests on those windows missed. The full broad schedule permits a different set of multipliers. [Coordinate tests](grouped-offset-rows.md) · [Public basis selector](../experiments/grouped_offset_frame.py)
