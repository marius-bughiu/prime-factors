# Testing the small-fraction search with fewer square roots

For a fraction of height at most $S$ to have a factor-revealing partner, there must be positive integers $h,v$ with $h v^2\le K=\lfloor(S-1)/2\rfloor$ such that $hN+v^2$ is an integer square. This gives two ways to search the same equations from the input alone. One scans the multiples $hN$, takes their next square roots and checks any gaps in range. The other chooses the gap $v$ first and uses small moduli to discard multipliers before taking a large square root. [Why the search covers every bounded pair](choosing-a-short-fraction.md)

On the 2,048-bit crossed control with $S=2^{22}$, the first search took **2,097,151** square roots of multiples and found zero gaps small enough for an extra square test. The second used a table of **4,032 residues**, visited 1,448 gaps and took **57,769** large square roots. Both finished the same search without a factor. One sequential run on an arm64 Mac using Python 3.9.6 took 7.66 and 0.22 seconds of CPU time respectively, including table construction. The 36-fold reduction counts large square roots; elapsed time depends on implementation and hardware. [Paired sieve benchmark](../benchmarks/seed-gap-sieve.json) · [Direct comparison](../benchmarks/guided-pairs.json) · [Verified progress page](https://marius-bughiu.github.io/prime-factors/)

## Which multipliers survive?

Take a modulus $M$ coprime to $N$. Precompute the sorted residues $N^{-1}s\bmod M$ for every distinct square $s$ modulo $M$, including zero. For each $v\le\sqrt K$, translate this table by $-N^{-1}v^2$. It lists exactly the residue classes of $h$ for which $hN+v^2$ is a square modulo $M$. Retrieve the part in $[1,\lfloor K/v^2\rfloor]$ using binary search in the cyclically shifted table. Try an integer square root only for a surviving pair, then use a gcd on any exact square. A wheel prime dividing the input can itself supply a factor. The algorithm records the source of its first factor. [Sieve and public counters](../experiments/seed_gap_sieve.py) · [Small exhaustive comparisons](../tests/test_seed_gap_sieve.py)

For $M=16\prod_{3\le p\le P}p$ the number of stored residues is $R=4\prod_{3\le p\le P}(p+1)/2$, with each product over primes. CRT constructs the table without scanning all of $M$. Once sorted, enumeration costs $O(\sqrt K\log(R+1)+C)$ operations on indices and table values, where $C$ is the number of surviving pairs. Each complete period reports $R$ candidates and pays for its own lookups. The initialization also costs $O(R\log R)$ operations for these bounded wheel primes. Each survivor requires a square test on the large integer. The gap count and table memory matter when comparing timings.

## A bound that holds for every input in the target family

For a fixed $v$ each complete block of $M$ multipliers has $R$ survivors. A final partial block has at most $R$. Use this count up to an integer $D\ge1$, then bound the remaining gaps by counting *all* their multipliers. Since $\sum_{v\ge1}v^{-2}<5/3$ and $\sum_{v>D}v^{-2}\le1/D$,
$$
C\le\left\lfloor\frac{5KR}{3M}\right\rfloor+DR+\left\lfloor\frac KD\right\rfloor .
$$
The elementary first estimate follows by summing the first five terms and bounding the tail by $1/5$. The budget evaluator uses $D=\max(1,\lfloor\sqrt{K/R}\rfloor)$. Evenly distributed incomplete blocks are unnecessary for this upper bound. For a 2,048-bit product whose two primes have 1,024 bits every modulus below is coprime to the input.

| At $S=2^{48}$ | Stored residues | Maximum large square tests | Reduction vs. a complete scan of $2^{47}-1$ multipliers |
|---|---:|---:|---:|
| Primes through 13, with modulus 240,240 | 4,032 | 3,938,219,551,248 | more than 35-fold |
| Primes through 19, with modulus 77,597,520 | 362,880 | 1,111,209,694,287 | more than 126-fold |
| Primes through 29, with modulus 51,757,545,840 | 65,318,400 | 487,777,227,415 | more than 288-fold |

These rows are worst-case counts for complete scans, computed without building the large tables. They quantify the potential improvement against the direct multiplier scan at this specified threshold. The input-population bound shows how seldom a fraction this small can work. Larger tables also leave a substantial cost even for the first gap. For $v=1$ alone there are at least $R\lfloor K/M\rfloor$ surviving multipliers on an exhausted search. [Lean filter, CRT count and 126-fold budget calculation](../PrimeFactors/SeedGapSieve.lean) · [Budget evaluator](../experiments/seed_gap_sieve.py) · [Proof and worked cases](choosing-a-short-fraction.md)
