# A square root halves the ordinary factor-sum sieve

For the 28-bit product 137,649,271, ordinary modular sieving left 40 possible factor sums. Requiring the factors to have positive Jacobi sign left 19. In increasing order, the factorization appeared at square test 22 with the ordinary sieve and test 14 with the extra condition. Both found 9,203 × 14,957. The searches used the same public modulus 119 and the same interval.

## Why the full-period counts differ by exactly two

Let the unknown odd factors have product $N$, and let $d$ be a public modulus coprime to $N$, with $d\equiv3\pmod4$. We have two public certificates with different jobs. A square root of $-d$ modulo $N$ implies by reciprocity that every odd divisor of $N$ has Jacobi symbol $+1$ modulo $d$. A square root $e$ of $N$ modulo $d$ explains how much this extra information rules out. [Divisor theorem](../PrimeFactors/ReciprocalDivisorClasses.lean) · [Factor-sum coverage](../PrimeFactors/ReciprocalDivisorSums.lean)

The ordinary sieve retains a sum $S$ whenever $S^2-4N$ is a square modulo $d$. Zero and squares of nonunits count. Equivalently, $S=x+N/x\pmod d$ for some unit $x$. If $x$ and $y$ give the same sum, reduce their equations modulo any prime $r\mid d$. Then $(x-y)(xy-N)=0\pmod r$. Either $y=x$ or $y=N/x$ there. In both cases $x$ and $y$ have the same quadratic character at $r$, because $N=e^2$ is a unit square there. Multiplying these local signs with the multiplicities of the primes in $d$ shows that **every pair giving the same sum has the same Jacobi sign**.

Negating $x$ negates its sum and reverses its Jacobi sign because $d\equiv3\pmod4$. This pairs every ordinary positive sum class with one negative class. The positive image therefore contains **exactly half of the ordinary square-discriminant classes modulo the same $d$**, including for composite moduli and repeated prime powers. The statement counts a full period. An interval can meet the two halves unevenly. The proof uses the prime divisors of $d$ to establish the identity. The experiment below computes the two sets without factoring $d$. [Lean proof](../PrimeFactors/ReciprocalTraceHalving.lean)

## Four complete interval searches

The inputs come from existing repository examples and were selected to illustrate different periods. Each search receives only the product, the common factor bit width and a continued-fraction budget. We combine the admissible sum classes modulo 60 with the classes modulo $d$ by the Chinese remainder theorem. We visit every retained sum in increasing order between the public factor-width bounds and check whether its integer discriminant is a square. Lean checked the product and primality of every pair in the table. [18-bit input](../benchmarks/radix-carries.json) · [28-bit inputs](../benchmarks/weighted-square-subsets.json) · [Three-prime period input](../benchmarks/quotient-search.json) · [32-bit input](../benchmarks/signed-discriminant-menu.json)

| Product and verified factors | $d$ | Local classes, ordinary → positive | Full interval, ordinary → positive | First successful test, ordinary → positive |
|---|---:|---:|---:|---:|
| 135,137 = 337 × 401 | 7 | 4 → 2 | 2 → 1 | 1 → 1 |
| 137,649,271 = 9,203 × 14,957 | 119 | 36 → 18 | 40 → 19 | 22 → 14 |
| 140,188,063 = 10,007 × 14,009 | 9,499 | 1,440 → 720 | 12 → 8 | 3 → 2 |
| 2,218,279,573 = 37,619 × 58,967 | 403 | 112 → 56 | 104 → 52 | 49 → 25 |

For 137,649,271, the anchor gives $e=72\pmod{119}$ and the interval is [23,465, 24,785]. Testing only the two signs at $S-2e$ and $S+2e$, after the ordinary sieve, keeps 21 candidates. Two of these, 23,740 and 24,692, reduce to 59 modulo 119. Both offset symbols vanish there. The only local factor pair giving 59 is $89,89\pmod{119}$, with negative Jacobi sign. Checking the actual positive-factor image removes both.

For 140,188,063, the ordinary table already has fewer entries than the orbit bound of 1,916 for the positive table. Modulo $9,499=7\cdot23\cdot59$, several different local factor pairs have the same sum. Counting distinct sums improves both sides. The exact comparison is 1,440 ordinary sums against 720 positive sums.

## Reading the sign without building the table

The same distinction can be read one sum at a time. Put $z=S-2e$. Split $d=uv$ so that $v$ contains the entire prime-power part of $d$ supported on primes dividing $z$. This takes a modular power and a gcd. With $L$ equal to the bit length of $d$, compute $v=\gcd(z^L\bmod d,d)$ and $u=d/v$. The exponent is $L$, so repeated squaring takes at most twice the bit length of $L$ modular multiplications.

For any ordinary sum with local factor $x$, the identity $x(S-2e)=(x-e)^2$ applies modulo $u$, where the minus offset is a unit. It follows that the Jacobi signs of $x$ and $S-2e$ agree there. At every prime dividing $v$, the plus offset is congruent to $4e$, a unit. Applying $x(S+2e)=(x+e)^2$ on that part gives the **exact** sign of $x$ modulo $d$.

$$
\left(\frac{x}{d}\right)
=\left(\frac{S-2e}{u}\right)\left(\frac{S+2e}{v}\right).
$$

For the extra residue 59 modulo 119, the split is $u=7$, $v=17$. The two signs of the split offsets are $-1$ and $+1$, recovering the negative factor sign even though the two whole-modulus symbols vanished. The public algorithm can evaluate the formula on the smaller of $S$ and $-S$ and assign the opposite orientation to its partner. On all four moduli the experiment exhaustively verifies that intersecting those selected residues with the ordinary sieve gives precisely the positive table. An individual sum that passes the orientation test still needs its integer square test. [Adaptive character](../PrimeFactors/ReciprocalAdaptiveCharacter.lean) · [Prime-power split](../PrimeFactors/SaturatedTraceSplit.lean) · [Orientation theorem](../PrimeFactors/OrientedTraceClasses.lean)

## What the counts cost

For the ordinary table, the program squares each integer from 0 through $\lfloor d/2\rfloor$ modulo $d$, using reflection to cover every root. The same loop counts the roots of $N$. It then checks the discriminant of each of the $d$ possible sums against the square table. For the positive table it computes one Jacobi symbol for each pair $x,-x$, drops the nonunits, and computes one inverse for the positive unit in each remaining pair. It keeps a single representative of each reciprocal pair $x,N/x$, then deduplicates equal sums.

| $d$ | Common anchor steps, scan + replay | Ordinary root candidates + sum lookups | Positive Jacobi calls + inversions | Reciprocal pairs before deduplication | CRT combinations, ordinary → positive |
|---:|---:|---:|---:|---:|---:|
| 7 | 32 + 15 | 4 + 7 | 3 + 3 | 2 | 8 → 4 |
| 119 | 128 + 97 | 60 + 119 | 59 + 48 | 25 | 216 → 108 |
| 9,499 | 4 + 3 | 4,750 + 9,499 | 4,749 + 3,828 | 1,916 | 5,760 → 2,880 |
| 403 | 32 + 19 | 202 + 403 | 201 + 180 | 91 | 448 → 224 |

The anchor scan and replay are common to this comparison. They include checking gcds and stripping small square factors from trial norms. The implementation of an ordinary sieve given $d$ does not require either root certificate. Building either CRT table also uses the common wheel of 16 units modulo 60 and one inverse of 60 modulo $d$. The operation counts have different costs. For example, the 9,499-period case has just 84 starting wheel candidates in its interval, so even the positive table requires far more setup operations than directly testing the 84 sums. This experiment establishes a reduction in the number of candidates. It gives no measured full-size running time.

Reproduce all four searches and regenerate the checked prime-factor certificates from the discovered factors with the following command. The script additionally verifies that the ordinary table agrees with exhaustive local factor pairs. This cross-check and certificate production are separate from the setup operation counts above. [Comparison program](../experiments/reciprocal_anchor_comparison.py)

```sh
python3 -m experiments.reciprocal_anchor_comparison --verify
```
