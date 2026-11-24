# Which polynomial choices give usable square relations?

On the same 16 freshly sampled 79-bit products, an ordinary interval of square differences recovered zero factorizations. Changing the polynomial every 1,025 positions recovered **six** at the same total number of positions. A second construction deliberately gave different polynomials some common prime factors. Using all the resulting cancellations recovered **five** products. Requiring every individual coefficient to cancel on its own recovered only **two** on exactly the same collected values. All five shared-coefficient successes were among the six square-coefficient successes. Lean verified both factors of each successful product. [All 16 inputs and outcomes](../research/polynomial-relations-panel.json) · [Reproducible fixtures](../benchmarks/polynomial-relations.json)

## Choosing the polynomial from the product

For an odd nonsquare input $N$, choose $A>0$ and $b$ with $b^2\equiv N\pmod A$. At each integer $x$ we compute

$$ Q(x)=Ax^2+2bx+(b^2-N)/A,\qquad (Ax+b)^2\equiv A Q(x)\pmod N. $$

With a known decomposition $A=c^2e$ and $c$ invertible modulo $N$, the left root $(Ax+b)/c\pmod N$ corresponds to signed norm $eQ(x)$. We retain $Q(x)$ if its absolute value factors completely into primes at most 2,048. A collection of rows can give a factor if the signed product of their norms is a square. We take the gcd of $N$ with the difference between its positive integer square root and the product of the corresponding left roots modulo $N$. A nontrivial gcd gives both factors for a semiprime. The search receives only $N$ and its public budgets. The choice of multiple sieve polynomials with square leading coefficients follows Montgomery's method as described by Silverman. [Silverman, *The Multiple Polynomial Quadratic Sieve*](https://doi.org/10.1090/S0025-5718-1987-0866119-8) · [Implementation](../experiments/polynomial_relations.py)

The three primary searches were fixed before measuring the panel. Each visited 64 blocks of 1,025 positions. We sampled the first 16 distinct 79-bit products of independent 40-bit primes from the deterministic byte stream seeded with `polynomial-relations-panel-v1`. The two independent prime streams supply labels for checking results. The public search uses neither stream. The ordinary method uses $A=1$ and visits all 65,600 consecutive integer roots starting at $\lceil\sqrt N\rceil$.

For the other two methods let $M=512$. To keep the polynomial values small on $[-M,M]$, aim for $A\approx\sqrt{2N}/M$. Choose splitting primes congruent to 3 modulo 4, larger than the factor bound, in order of proximity to $\lfloor\sqrt{\lfloor\sqrt{2N}\rfloor/M}\rfloor$, with the smaller prime first on a tie. Each root is proposed by modular exponentiation and verified. Represent $b$ between $-A/2$ and $A/2$.

* For a **square coefficient** use each of the first 64 such primes $s$ once. With $A=s^2$ we lift a root of $N$ to $s^2$. Here $c=s$ and $e=1$.
* For a **shared coefficient** take the nine nearest such primes. For each pair $s,t$, in the order of their indices, use $A=st$. Fix one sign at $s$ and try both signs at $t$, combining the roots by CRT. Use the first 64 polynomials in this order. Here $c=1$ and $e=st$. This selects 32 distinct coefficients.

For large inputs we first extract a common square scaling factor. If the target for $s$ exceeds 65,535, choose the smallest available odd splitting prime $l$ of the factor base. Take the least $j$ for which the target divided by $l^j$ is at most 65,535, and select the auxiliary primes around this reduced target. Multiply every $A$ by $l^{2j}$, choose a root of $N$ modulo that prime power by Hensel lifting and combine it with the coefficient-specific root. The known square factor $c$ then contains $l^j$. The fixed auxiliary-prime catalogue ends at 131,071. The program reports any insufficient supply of coefficient primes. This construction needs no sampled large primes or hidden factor information.

## How the work was counted

For every factor-base prime, we solve $Q(x)=0$ modulo that prime and visit its progressions in a block. When the prime divides $A$, this is a linear equation in $x$. One mark is one visit to a position at a prime. Each successful division by that prime counts separately, including repeated powers. The sieve is exact. It keeps signs and exponents modulo two, and retains a row only when the remaining cofactor is one. Binary elimination counts independent square dependencies on the completed panel. We take gcds as new basis dependencies appear until the first split. Continuing the sieve and rank computation through the fixed budget makes row counts comparable across methods.

| Search | Positions | Sieve marks | Prime divisions | Smooth rows | Independent square dependencies | Gcds tried | Products split |
|---|---:|---:|---:|---:|---:|---:|---:|
| Ordinary interval | 1,049,600 | 2,225,363 | 3,064,570 | 251 | 0 | 0 | 0 |
| Square coefficients | 1,049,600 | 2,225,419 | 3,064,693 | 1,901 | 224 | 8 | 6 |
| Shared coefficients | 1,049,600 | 2,225,601 | 3,064,868 | 1,984 | 207 | 8 | 5 |

In a sensitivity check **after** the primary comparison we centered the one-polynomial interval around $\sqrt N$ while retaining its 65,600 positions per product. This yielded 343 smooth rows, zero dependencies and zero factorizations. The public root tables through 2,048 cost 288,867 modular-square insertions once; all methods can share them. With those tables and the auxiliary-prime catalogue precomputed, one sequential arm64 Mac run took 0.84, 0.89 and 0.89 CPU seconds respectively across all 16 inputs, including the parity comparisons. Table and catalogue initialization took 0.04 seconds. These are small-input measurements. [Cases, sieve and setup counters](../research/polynomial-relations-panel.json)

## The contribution from sharing coefficient primes

A row from $A=st$ has one incidence at each of the two primes $s,t$. Think of those two primes as vertices joined by an edge. Since $s,t$ exceed the factor bound, their exponents in $Q(x)$ are zero on every retained row. An exact square requires even degree at every vertex and even aggregate parity in the signed factor base. Cycles allow an odd number of rows from an individual edge. The classical two-large-prime method uses a graph on cofactors found after sieving. Here the vertices and edges are deliberately chosen in the leading coefficients before sieving. [Lenstra and Manasse, *Factoring with Two Large Primes*](https://electronicsandbooks.com/edt/manual/Magazine/M/Mathematics%20of%20Computation/1960-2002/pdf/1994_v063_n208/2153299.pdf)

There is an exact rank interpretation. Let $P$ send a selection vector of rows to its signed small-prime parities, $E$ to its parity on each distinct coefficient edge, and $D$ send an edge selection to the degrees modulo two. The full dependency space is $\ker P\cap\ker(DE)$. The per-coefficient restriction is $\ker P\cap\ker E$. The image of the first space under $E$ is precisely $E(\ker P)\cap\ker D$, and its kernel there is the restricted space. Thus the gain in dimension is the dimension of the realizable cycle parities. Per-polynomial labels impose one more condition whenever the two choices of root at one coefficient occur an odd number of times each. [Independent parity and square checks](../tests/test_polynomial_relations.py)

| Requirement on the same 1,984 smooth rows | Independent square dependencies | Gcds tried | Products split |
|---|---:|---:|---:|
| Even degree at each of the nine auxiliary primes | 207 | 8 | 5 |
| Even row count for each distinct coefficient | 130 | 3 | 2 |
| Even row count for each signed polynomial | 71 | 6 | 2 |

On $563377948785282057047021$ the shared search found $591389861983\times952633761587$ using 64 rows at position 57,115. Eighteen coefficient edges appeared an odd number of times. At the full 65,600-position budget it had 17 independent dependencies. Requiring every coefficient to appear evenly left zero dependencies among the same 166 rows. The square-coefficient search found the same factors at position 61,959. The first successful shared dependency on each of the five inputs used at least one edge an odd number of times. [Checked fixtures and controls](../benchmarks/polynomial-relations.json)

On the established 2,048-bit crossed control each of the three methods visited 65,600 positions at the same cutoff 2,048. They made respectively 189,579, 167,685 and 167,819 sieve marks. None produced even one smooth row, and the entire input remained unresolved. This comparison establishes the contribution of coefficient choices and cycle cancellations in the stated sample. It gives no practical factoring bound at 2,048 bits. Reproduce the panel and its 16 Lean certificates with `python3 -m experiments.polynomial_relations --panel --verify`.
