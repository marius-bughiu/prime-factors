# Reading a factor bit without building the factorial coefficient

An earlier proof gave an integer coefficient whose gcd with the input tells us whether the two primes differ at a particular binary digit. At 2048 bits even the first coefficient needs over $2^{1024}$ bits to write down. We found a way to obtain that gcd by testing ordinary divisors in an interval determined by the input. On the fresh 2048-bit control the first interval is empty, so we can prove the exact answer with no candidate multiplications. Its value is the entire input, and the factors remain unresolved. [Earlier factorial readout](dyadic-totative-masks.md) · [New interval proof](../PrimeFactors/DyadicFactorBands.lean)

## Where the first differing digit can occur

Write $N=pq$ with distinct odd primes $p<q$ of the same bit length. Let $s=\lfloor\sqrt N\rfloor$. For a cell width $d$ put $a=d\lfloor s/d\rfloor$ and $b=a+d$. The two factors have the same quotient on division by $d$ precisely when both are in the same interval $[a,b)$ as the square root. Since $p\le s<q$, this requires $p\ge a$ and $q<b$. The second condition is equivalent to $p>\lfloor N/b\rfloor$. Consequently
$$
\lfloor p/d\rfloor=\lfloor q/d\rfloor
\quad\Longleftrightarrow\quad
p\ge \max(a,\lfloor N/b\rfloor+1).
$$
The right-hand side is a single public cutoff for the unknown smaller prime. The equivalence itself holds for any ordered positive factors.

Let $T_j$ be the cutoff for $d=2^j$. Read binary digits from high to low, numbering the units digit zero. Then **the highest digit at which the primes differ is $j$ precisely when $T_{j+1}\le p<T_j$**. The cutoffs rise as the cells shrink. Every candidate belongs to at most one band, and exactly one band contains the genuine smaller prime. Intersect each band with the known smaller-factor interval and, if desired, remove multiples of the small primes in a wheel coprime to $N$. [Exact criterion, unique band and disjointness](../PrimeFactors/DyadicFactorBands.lean)

Multiply the remaining candidates modulo $N$ and take a gcd. On the successful band this returns $p$. Before that point, the two primes agree in the current bit, which is also the bit of $s$. The old coefficient gcd on a completed unsuccessful band is therefore $N$ if that bit of $s$ is one, and one otherwise. A partially tested band can certify a split as soon as it finds a factor. Its incomplete product cannot certify a miss.

For example, $3127$ has square root between 55 and 56. The first eligible band of smaller-factor candidates is empty and the inferred gcd is 3127. The next band, clipped to the known smaller-factor interval, contains the integers from 50 through 55. Removing multiples of 2, 3 and 5 leaves only 53. A single modular multiplication and a gcd give $3127=53\cdot59$.

## What the work costs

The running interval product always fits in a residue modulo $N$. Computing the cutoffs needs integer divisions and a single square root for the whole schedule. The simple evaluation scans the surviving wheel candidates. With a fixed wheel and streamed output, it uses $O(\log N)$ bits of working memory and at most $\lfloor\sqrt N\rfloor$ candidate multiplications for the complete schedule. Classical fast factorial and multipoint algorithms can also evaluate such interval products in blocks. On a complete sweep the bands are disjoint pieces of the repository's existing smaller-factor interval. Their total raw width cannot exceed that interval. Each new block evaluation has its own setup cost. The reduction makes the factorial-bit information accessible with conventional factoring work and gives no general improvement over the fastest factoring methods. [Repository interval-product implementation](factorial-progressions.md) · [Bostan, Gaudry and Schost](https://doi.org/10.1137/S0097539704443793) · [Costa and Harvey](https://arxiv.org/abs/1201.2116)

The experiment used the product alone, a wheel of 30 and a cap of 4,096 integer positions across all bands. Expected factors were checked after the search. A modular multiplication in the table means one candidate was multiplied into the current product. Computing the cutoffs, generating residues and taking gcds add work.

| Product | Raw positions examined | Modular multiplications | Result |
| --- | ---: | ---: | --- |
| 2257 | 12 | 4 | $37\times61$ |
| 3127 | 6 | 1 | $53\times59$ |
| 1763 | 10 | 2 | $41\times43$ |
| 137,549,339 | 2,798 | 746 | $8693\times15823$ |
| Fresh 2048-bit control | 4,096 | 1,092 | First bit read exactly, second band unfinished |
| Crossed 2048-bit control | 4,096 | 1,092 | First band unfinished |

The fresh control exceeds three quarters of $(2^{1024})^2$. Since each factor is smaller than $2^{1024}$, each must exceed $3\cdot2^{1022}$. Both second-highest bits are one. The fixed proof uses the project's existing prime certificates to check the resulting factorial-coefficient gcd without evaluating the coefficient. The next fresh-control band has a 1,021-bit width and the first crossed-control band has a 1,022-bit width. These are sizes of actual windows, with both products unresolved after the cap. [Inputs and budgets](../benchmarks/dyadic-factor-bands.json) · [Experiment and fresh-control proof generator](../experiments/dyadic_factor_bands.py)

Run `python3 experiments/dyadic_factor_bands.py --fixtures` for the six searches. To check the full-size gcd, run `python3 experiments/dyadic_factor_bands.py --fresh-proof build/DyadicFreshProof.lean` followed by `lake env lean build/DyadicFreshProof.lean`. The remaining question is whether some product-derived measurement can cheaply select a much shorter subinterval inside a nonempty band.
