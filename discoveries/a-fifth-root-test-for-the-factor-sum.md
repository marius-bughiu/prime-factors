# A fifth-root test for the factor sum

Let $N=pq$ for distinct odd primes other than 5. One value of the public-index cyclotomic polynomial, $\Phi_N(3)\bmod 11$, determines $p+q\bmod 5$. This is a reduction to an exact evaluation. The size of the output is four bits, but the usual binary product formula needs the residues of the unknown primes. A separate public square test sometimes supplies enough information to recover the sum. [Lean proof](../PrimeFactors/CyclotomicSmallNorm.lean)

## What the evaluation reveals

The four primitive fifth roots in $\mathbb F_{11}$ are $3,4,9,5$. At any of them, the binary cyclotomic identity reads

$$
 \Phi_{pq}(x) = \frac{(x^{pq}-1)(x-1)}{(x^p-1)(x^q-1)}.
$$

All exponents may be reduced modulo 5. If one prime is 1 modulo 5, the value at 3 is 1 and $p+q\equiv N+1\bmod 5$. The other six unordered pairs give the following complete table. The proof checks the identity directly in the finite field. Bzdęga, Herrera-Poyatos and Moree give the classical complex fifth-root evaluation in Lemma 28, and a general formula in terms of characters and the primes dividing the index. [Original paper](https://arxiv.org/abs/1611.06783)

| Unordered residues of the primes mod 5 | 2,2 | 2,3 | 2,4 | 3,3 | 3,4 | 4,4 |
|---|---:|---:|---:|---:|---:|---:|
| $\Phi_N(3)\bmod 11$ | 8 | 7 | 4 | 10 | 5 | 9 |
| $p+q\bmod 5$ | 4 | 0 | 1 | 1 | 2 | 3 |

Multiply the values at 3 and 4. The result is 3 if both primes are nonsquares modulo 5 and 1 otherwise. When $N\equiv1,4\bmod 5$, both primes have the same quadratic character modulo 5. Quadratic reciprocity and the Chinese remainder theorem then give

$$
 \Phi_N(3)\Phi_N(4)\equiv 1\bmod 11
 \quad\Longleftrightarrow\quad 5\text{ has a square root modulo }N.
$$

Multiplying over all four primitive roots always gives 1. For any fixed input modulus $T>0$, Dirichlet's theorem gives arbitrarily large pairs of distinct odd primes whose products both equal 1 modulo $5$ and $T$, with different two-point values. Thus a lookup at $N\bmod T$ cannot determine this bit throughout the unbounded domain. The argument gives no equal-width guarantee for those pairs and no lower bound for general algorithms. For a finite example, 341 and 91 agree modulo 250 and give 1 and 3 respectively. [Exact statements and examples](../PrimeFactors/CyclotomicSmallNorm.lean)

## A factor sum from the product alone

For $N\equiv4\bmod5$, a public witness $x^2=kN+5$ supplies a square root of 5 modulo $N$. Both prime factors must therefore be squares modulo 5. Their product class 4 forces their residues to be 1 and 4, so $5\mid p+q$. The direct rule fixes $k=1$ and tests whether $N+5$ is a square. An unsuccessful probe leaves the product unresolved.

Take $N=174719$ with the promise of two distinct 9-bit prime factors. The single probe succeeds because $418^2=N+5$. The product and the upper prime bound 511 give $836\le p+q\le852$. The lower bound is the ceiling of $2\sqrt N$. The upper bound follows from $(511-p)(511-q)\ge0$. Because $N\equiv3\bmod4$, the possible sums are 836, 840, 844, 848 and 852. Only 840 is divisible by 5. Its discriminant $840^2-4N=82^2$ gives the certified factors 379 and 461. The reconstruction uses one square probe and one discriminant test. Ordinary Fermat factorization uses three consecutive midpoint tests here, in addition to its starting square root. [Benchmark fixture](../benchmarks/cyclotomic-small-norm.json)

Among all 903 unordered pairs of distinct 9-bit primes, 218 products pass the initial class-4 check and exactly one passes the square probe. It is the example above. The other 902 products produce no factor by this rule. Run <code>python3 -m experiments.cyclotomic_small_norm</code> to reproduce the census. The program supplies only the product, the common width and a test cap to the search. [Census and search](../experiments/cyclotomic_small_norm.py)
