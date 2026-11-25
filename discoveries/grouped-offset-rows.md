# Counting a trillion offset tests a row at a time

On the fresh 2,048-bit product, there are 1,099,511,627,776 possible offsets in this experiment. We reduced them to 41,878,707,496 distinct candidates that pass two necessary square tests. The count took 2.25 seconds on one local run. A separate run tested 64 of the survivors and found no factor. The same search on 2,376,225,323 checked six survivors and recovered **36,559 × 64,997**. [Full-size counts](../research/grouped-offset-rows.json) · [Executable comparison](../experiments/grouped_offset_rows.py) · [Why offset 13 works on the smaller example](grouped-norm-offsets.md)

## Which offsets can be grouped?

Let $T=\lfloor\sqrt N\rfloor$ and $h=N-T^2>0$. For each $1\le j\le J$ take $k=\lfloor(Tj-1)/h\rfloor$ and keep $k>0$. The test looks for an integer square
$$F(j,k)=j^2+4k(Tj-hk).$$
If $j,k$ have a common divisor $g$, the test scales by $g^2$. The reduced pair still uses the top multiplier at its own offset. For the large comparisons each such $g\le J=2^{40}$ is smaller than either promised prime and is a unit modulo $N$. Thus reducing to coprime pairs preserves the chance of recovering either prime. For other inputs a common divisor of $g$ and $N$ can itself produce a factor. This count and the bounded row search measure the primitive tests. [Normalization and factor extraction](../PrimeFactors/GroupedNormOffsets.lean)

Choose a reduced approximation $A/B$ to $T/h$ with $1\le B\le\lfloor\sqrt J\rfloor$ and $|BT-hA|\le h/(\lfloor\sqrt J\rfloor+1)$. The last continued-fraction convergent with denominator in range suffices. Choose $C,D$ with $BD-AC=1$. Write every pair uniquely as
$$j=Br+Ct,\qquad k=Ar+Dt.$$
In particular $t=Bk-Aj$, $r=Dj-Ck$, and $\gcd(j,k)=\gcd(r,t)$. With $e=BT-hA$ we have $ht=ej-B(Tj-hk)$. The allowed ranges $1\le Tj-hk\le h$ and $1\le j\le J$ therefore give a range of length at most $B+|e|J/h$ for $t$. The default frame visits at most $O(\sqrt J)$ rows. For fixed $t$, the two inequalities on $j$ and $Tj-hk=er+(CT-hD)t$ give exactly one integer interval for $r$. The implementation includes all endpoints and handles zero slopes. [Coordinate, row and span identities](../PrimeFactors/GroupedOffsetRows.lean) · [Bounded approximation](../PrimeFactors/RootIntervalSlope.lean)

## Two necessary conditions on a whole row

For every coprime pair giving an integer square, **$F(B,A)$ must be a square modulo $|t|$ and $F(C,D)$ must be a square modulo $|r|$**. For example, reduction modulo $t$ gives $F(j,k)\equiv r^2 F(B,A)$. The inverse of $r$ exists modulo $|t|$, so a square root of $F(j,k)$ gives one of $F(B,A)$. The other axis follows by exchanging the two basis vectors. At zero modulus the congruence means exact equality and the other coordinate is a unit. Lean proves both implications over the integers, including zero. [Lean proof](../PrimeFactors/GroupedOffsetRows.lean)

The full screen factors coordinate magnitudes up to their public bounds. An odd prime not dividing the pivot discriminant forbids its multiples exactly when the discriminant is a nonsquare modulo that prime. For a prime dividing the discriminant, the first obstructing power depends on the valuation and the unit left after removing that power. At two, the odd unit must be 1 modulo 8 once three digits are exposed. For example, on the fresh input the first coordinate filter also excludes multiples of 8 or 9. The second excludes multiples of $41^2$. A pivot value of zero is a square for every modulus. [Local square classification](counting-local-midpoints.md) · [Implementation and direct checks](../tests/test_grouped_offset_rows.py)

After excluding whole rows, the counter sums over squarefree divisors of $|t|$ to count coprime $r$ in its interval by inclusion-exclusion. A prefix table counts signed multiples that avoid the rejecting primes on the second axis. Higher forbidden prime powers are included by an additional short inclusion-exclusion, using the least common multiple with each divisor. Zero and the row $t=0$ are counted separately. The bounded search can visit the surviving coordinate values in ascending row order and check their original discriminants. When the second coordinate would exceed the configured memory limit, the program reports just the first-axis count and can search using that filter. Both full-size comparisons fit.

| Comparison | Distinct primitive pairs | Rows visited | Passing both tests with odd primes through 251 | Passing the full two-axis tests | Time for full count |
| --- | ---: | ---: | ---: | ---: | ---: |
| Fresh | 668,422,917,531 | 420,117 | 200,826,035,207 | 41,878,707,496 | 2.25 s |
| Crossed | 668,422,918,155 | 750,667 | 185,267,915,529 | 35,042,535,262 | 3.72 s |

The two axes discard 93.73% and 94.76% of distinct primitive pairs, respectively. These counts concern necessary conditions only. A factorization still requires a square discriminant and a proper divisor. The aggregate counts come from integer arithmetic independently checked against direct enumeration on bounded inputs. On each large comparison a separate Lean certificate rejects an explicit whole row. For both products the first 64 retained candidates in row order returned no factor. [Arithmetic receipts](../research/grouped-offset-rows.json) · [Whole-row certificates](../PrimeFactors/GroupedOffsetRowExamples.lean) · [Frequency across balanced prime products](offset-sweep-frequency.md)

Choosing the two directions by their modular conditions reduced the number of surviving candidates further and increased the time required to count them. The selected frame left 19,374,937,700 on fresh, compared with 41,878,707,496 here. [Matched comparisons](choosing-offset-rows.md)

## What Dirichlet GRH can guarantee

For a nonsquare, nonzero integer pivot discriminant $d$, take the quadratic field of $\sqrt d$. Its fundamental discriminant divides $8|d|$. The attached quadratic character is nontrivial on the units modulo $q=8|d|$. On an odd prime outside $q$, its value is the Legendre symbol of $d$. Under Dirichlet GRH, the small-prime-outside-a-subgroup theorem applied to its kernel bounds the least rejecting prime by $(\log q+B(q))^2$ for $q\ge3000$, with $B(q)$ as in that theorem. This guarantees a prime that rules out all primitive rows whose index is a multiple of it. The bound alone need not put a rejecting prime inside a given short set of row indices. The measured counts use explicit integer-square tests at prime powers and are unconditional. [Lamzouri, Li and Soundararajan, Theorem 1.1](https://arxiv.org/html/1309.3595v3#S1.SS1) · [Dirichlet statements in the pinned Riemann repository](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)
