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

For the comparison, both searches assume distinct odd prime factors of the same specified width $b$. Let $L=2^{b-1}+1$, $H=2^b-1$, and $c=\lceil\sqrt N\rceil$. Their common interval starts at $2c$ and ends at the largest even integer no greater than $\min(L+\lfloor N/L\rfloor,H+\lfloor N/H\rfloor)$. Both searches use one boundary square root. Comparing $N$ with $LH$ selects the tighter upper endpoint before division, so each search uses one upper-bound division. Testing $c^2=N+5$ adds one square and equality comparison. It reuses the boundary root.

The ordinary sum search applies the repository's stride $W\in\{4,8,12,24\}$, which gives $S\equiv N+1\bmod W$. It also applies the ordinary mod-5 table, which permits $S\bmod5\in\{0,1,4\}$ when $N\equiv4\bmod5$. Both searches check remaining sums in ascending order. Each discriminant test takes a square root of $S^2-4N$. [Stride proof](../PrimeFactors/CyclotomicRadixLift.lean)

| $N$ | Factor width | $W$ | Even interval | Ordinary candidates | After probe | Discriminant tests, ordinary / probe | Fermat midpoint tests |
|---:|---:|---:|---|---|---:|---:|---:|
| 174719 | 9 | 24 | 836–852 | 840 | 840 | 1 / 1 | 3 |
| 419899 | 10 | 8 | 1296–1330 | 1300, 1316, 1324 | 1300 | 1 / 1 | 3 |
| 2748959 | 11 | 24 | 3316–3388 | 3336, 3360, 3384 | 3360 | 2 / 1 | 23 |

The 9-bit control already has a unique sum from the stride alone. On 419899 the probe excludes two possibilities, but ordinary search reaches the correct sum first. Ordinary mod-7 testing also leaves only 1300 on that input. The last row is the first that saves a discriminant check. There $1658^2=N+5$ forces $5\mid S$, and only 3360 remains. The discriminant is $542^2$, giving the certified factors 1409 and 1951. Ordinary tests modulo 7, 9 and 11 together preserve all three candidates. Adding mod 13 removes the earlier false candidate, so ascending search also succeeds in one discriminant check. Mod 25 alone leaves only 3360. Each Fermat comparison in the table also uses one setup root to find its starting midpoint. [Native benchmark and expected work](../benchmarks/cyclotomic-small-norm.json)

The census enumerates all 13,358 unordered pairs of distinct odd primes with equal width from 2 through 11 bits, allowing products of either possible bit width. It orders by width and then by increasing product. Of these, 3,305 products meet the preliminary mod-5 condition, eight satisfy $N+5=c^2$, and two have at least two ordinary candidates and exactly one probe candidate. The first such product is 419899. The first with a full $2b$-bit product, and the first to save a discriminant check, is 2748959. The earlier 9-bit census contains 903 products, 218 probes and one successful square test, which is the redundant 174719 control. These counts cover the stated finite population. Run <code>python3 -m experiments.cyclotomic_small_norm</code> to reproduce them. [Census and search](../experiments/cyclotomic_small_norm.py)

## How rare is the clue at 2,048 bits?

Count each unordered pair of distinct 1,024-bit primes whose product has 2,048 bits once. **Fewer than one in $2^{1000}$** of these products can satisfy $N+5=x^2$. The same bound holds for any fixed nonnegative offset, however large. Trying up to $2^{40}$ different offsets chosen before seeing the product still covers fewer than one in $2^{960}$. For a fixed offset the possible roots lie in a short interval and have one parity. Each root determines its product, which in turn determines at most one of the prime pairs. [Root count and finite-population proof](../PrimeFactors/SmallNormSquarePopulation.lean)

A possible extension is to look at the first $2^{40}$ integers $a$ starting at the ceiling of the square root of $N$, and accept any $a^2-N=h u^2$ with $h$ at most $2^{64}$. This allows the square part $u^2$ to be arbitrarily large. Even granting every such coefficient and free recognition, fewer than one in $2^{403}$ eligible products have any qualifying midpoint. Within this range the excess is less than $2^{1066}$, so $u<2^{533}$ for positive $h$. All the possible excesses therefore fit in a fixed menu of at most $2^{597}$ offsets. A product of two distinct primes cannot already be a square. [Bound for the extended search](../PrimeFactors/SmallNormSquarePopulation.lean)
