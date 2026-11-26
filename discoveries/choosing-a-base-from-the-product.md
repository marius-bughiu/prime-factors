# Can the product tell us which base to try?

Yes on some inputs. Starting from **135,137**, we added or subtracted one and looked for a base dividing either neighbor. After ten remainder checks, base 41 led to **337 × 401**. Lean proved that every power-of-two base in the same range misses this pair when the lower correction is between −4 and 4, however we choose the upper correction. [Checked search](https://marius-bughiu.github.io/prime-factors/#radix-carry-neighbors-135137) · [Lean proof of the success and the misses](../PrimeFactors/NeighborRadixExample.lean)

## Where the answer came from

Since $135{,}137=41\times3296+1$, we know the remainder at base 41 is 1. Dividing by $41^2$ and rounding gives 80. Using upper correction zero and lower correction $-2$ in the rounded-digit formula gives the proposed sum $80\times41+3296+2=6578$. The difference between the two corresponding numbers is $\sqrt{6578^2-4\times80\times135{,}137}=162$. The larger number is 3,370. Its greatest common divisor with 135,137 is 337. Dividing the original number by 337 gives 401. The search tried six correction pairs, three of which required square-root tests. [Formula for arbitrary positive bases](factoring-from-two-rounded-digits.md) · [Benchmark settings](../benchmarks/radix-carries.json)

We tried both choices of base on **all 543** unordered pairs of distinct 9-bit primes whose products have 18 bits. Both searches used correction limits of four. The first tested the five powers of two from 32 to 512. The second kept every base from 32 to 512 dividing either neighbor. Each search received only the product. A prime pair was used to check its search result after the search finished.

| Searches that found a factor | Products |
|---|---:|
| Both | 445 |
| Powers of two only | 59 |
| Bases dividing a neighbor only | 34 |
| Neither | 5 |

Overall, the five fixed bases found 504 of 543 pairs. The neighbor rule found 479 and spent up to 481 extra remainder checks per product to select its bases. We selected 135,137 from the 34 products found only by the neighbor rule. The following reproduces the full comparison from the repository root.

~~~python
from collections import Counter
from itertools import combinations
from experiments.radix_carries import search, search_neighbors
from scripts.factor import primes_through

counts = Counter()
for p, q in combinations([p for p in primes_through(511) if p >= 256], 2):
    n = p * q
    if n.bit_length() == 18:
        d, _ = search(n, 4, 4)
        a, _ = search_neighbors(n, 4, 4, 481)
        assert d in (None, p, q) and a in (None, p, q)
        counts[d is not None, a is not None] += 1
print(counts)
~~~

## What happens on 2,048-bit inputs?

Consider the much more powerful version which can obtain **every** divisor of $N-1$ and $N+1$ for free. It may choose any of those bases from $2^{513}$ through $2^{1024}$ after reading all the digits of $N$. It may also choose an arbitrary upper correction. For uniformly chosen distinct 1,024-bit primes conditioned on a 2,048-bit product, the fraction recoverable by this rule is below $2^{-472}$ with lower corrections through $\pm4$. Even extending them through $\pm2^{357}$ leaves the fraction below $2^{-117}$. These are upper bounds on the chance of finding a factor, including accidental square hits. They do not assume a particular implementation or a cost for obtaining the divisors. [Population theorem](../PrimeFactors/NeighborRadixPopulation.lean)

Here is why allowing so many bases still leaves a restriction. For a base $D$ dividing one of the two neighbors, the rounded remainder of $N$ is $1$ or $-1$. A successful lower correction $k$ forces the product of the two hidden factor remainders to be $kD+1$ or $kD-1$. Every signed factorization of this integer fixes **both** prime residues modulo $D$. We bound how many such factorizations can occur as $D$ varies between consecutive powers of two. For a given small divisor $m$ of $kD\pm1$, the possible bases lie in one residue class modulo $m$. Summing these counts over $m$, over both neighbors, and over the permitted lower corrections gives the stated limits. Lean checks the finite counting bounds. The population denominator uses the same published unconditional prime counts as in the earlier calculation. [Divisor count across bases](../PrimeFactors/NeighborRadixDivisors.lean) · [Prime-count premise](factoring-from-two-rounded-digits.md#how-many-ordinary-products-could-it-reach)

Mackall's digit-polynomial method also uses potentially nonbinary bases. Its full search can try bases that divide neither neighbor. Our bound covers the particular rule of choosing divisors of $N\pm1$ in the specified range. Finding a cheap rule with broad coverage for ordinary inputs remains open. [Mackall's method](https://eoinmackall.github.io/files/papers/factorization.pdf)
