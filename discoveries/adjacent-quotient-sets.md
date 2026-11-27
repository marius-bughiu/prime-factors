# What changes in the quotient table when the product decreases by one?

For a product of distinct odd primes, two tables computed from the product alone exchange just one number. The new entry is the larger prime. On the largest small example below, the tables each contained 7,061 entries. Ordinary division found the smaller prime after 917 tests.

## The exchange

Let $N=pq$ with $p<q$ prime, and let $H=\lfloor\sqrt N\rfloor$. For $n=N$ and $n=N-1$, form the *set* of integers $\lfloor n/k\rfloor$ for $2\le k\le H$. The sets agree except for $q$ in the first and $q-1$ in the second. Indeed, changing $N-1$ to $N$ changes a quotient only if $k\mid N$. The sole such denominator is $p$. For $k<p$, the quotient of $N$ exceeds $q$. For $k>p$, it is less than $q-1$, since $q\ge p+2$. This excludes collisions with any other entry. Lagarias and Richman study the arithmetic of floor-quotient sets. The previous repository result recovers the smaller prime by summing weighted jumps over denominator positions. [Lean exchange and rank formulas](../PrimeFactors/AdjacentQuotientSets.lean) · [Lagarias and Richman, 2024](https://arxiv.org/abs/2212.11689) · [Earlier prefix formula](floor-sums-at-the-factor.md)

There is a cheap way to count the entries at least $y>0$. Whenever $H^2\le n$, the quotients decrease strictly on the specified denominator range, so the count is $\max(0,\min(H,\lfloor n/y\rfloor)-1)$. For the two inputs these counts differ only when $y=q$. Both a threshold smaller than $q$ and a threshold larger than $q$ give equal counts. One such comparison cannot choose the direction of a binary search. Enumerating the full two sets costs $2(H-1)$ quotient divisions.

## Computing the totient twice

Write $\Phi(n)=\sum_{j=1}^n\varphi(j)$. Its adjacent difference gives $\varphi(N)$, hence $p+q=N+1-\varphi(N)$. Our comparison uses the elementary recurrence $\Phi(n)=n(n+1)/2-\sum_{k=2}^n\Phi(\lfloor n/k\rfloor)$, which follows by summing $\sum_{d\mid j}\varphi(d)=j$. It sieves a prefix through $H$, visits equal-quotient blocks together, and caches every larger argument. Descending again from a quotient gives another quotient of the initial number, since $\lfloor\lfloor n/k\rfloor/j\rfloor=\lfloor n/(kj)\rfloor$. Every quotient above $H$ occurs on the first descent or at the root. When evaluating $N-1$ with that cache, the only new large arguments are $N-1$ and $q-1$. Even if the first cache is free, the second root alone visits at least $2^{1023}-1$ distinct quotient blocks on every 2,048-bit input. The denominators from 2 through $2^{1023}$ already have that many distinct quotients. Brown describes a different algorithm for a standalone summatory totient, with time $\widetilde\Theta(n^{2/3})$ and space $\widetilde\Theta(n^{1/3})$. [Lean two-state result](../PrimeFactors/AdjacentQuotientSets.lean) · [Brown, 2025](https://arxiv.org/abs/2506.07386)

| Product | Prime factors | Keys per set | Sieve updates | Blocks for first sum | Additional blocks for second sum | Odd trial divisions |
|---:|---|---:|---:|---:|---:|---:|
| 34,387 | 137 × 251 | 184 | 339 | 9,072 | 397 | 3 |
| 132,079 | 269 × 491 | 362 | 710 | 25,709 | 766 | 7 |
| 3,641,921 | 1,811 × 2,011 | 1,907 | 4,237 | 323,054 | 3,901 | 231 |
| 49,884,889 | 6,827 × 7,307 | 7,061 | 16,873 | 2,335,970 | 14,291 | 917 |

Each summatory block takes two quotient divisions. The sieve column counts one update per prime multiple through $H$, followed by $H-1$ prefix additions. Trial division begins at the first odd integer at least $\lceil\sqrt{N/2}\rceil$, using the balanced promise $q\le 2p$. The first two products are prior floor-sum controls. For each of 11 and 13 bits, the last two use the first two primes found in the upper quarter of that bit range by Python's Random(20261127), drawing odd candidates uniformly. All three calculations receive only the product. Lean certifies the eight primes and four products. Run the comparison script to check the work counts and decimal answers. [Comparison script](../experiments/adjacent_quotient_sets.py) · [Fixture](../benchmarks/adjacent-quotient-sets.json)
