# A factor outside the tested block

For $N=157601$, the nine integers from 392 to 400 are all coprime to $N$. The adjacent smaller integer 391 is also coprime. Yet two polynomials representing the nine positions produce a Euclidean remainder whose leading coefficient shares the factor 439 with $N$. The product alone determines the center $t=\lfloor\sqrt N\rfloor=396$. Lean checks both prime factors, $359\cdot439=157601$, and the gcds. [Proof](../PrimeFactors/BlockSubresultantProbe.lean)

## Where the extra test comes from

Take an odd block width $m=2h+1\ge3$. Let $F$ be monic with roots $i$, and $G$ monic with roots $t+mj$, for $-h\le i,j\le h$. Up to sign their resultant multiplies the $m^2$ consecutive integers $t+mj-i$. Euclid’s algorithm also computes intermediate coefficients. The coefficient at degree $m-2$ gives a separate test before reaching this resultant. The relation of polynomial remainder sequences and principal subresultants is classical. [Brown and Traub, 1971](https://iiif.library.cmu.edu/file/Traub_box00027_fld00059_bdl0001_doc0001/Traub_box00027_fld00059_bdl0001_doc0001.pdf)

Write $F-G=uX^{m-1}+vX^{m-2}+wX^{m-3}+\cdots$, and let $f_2$ be the coefficient of $X^{m-2}$ in $F$. The coefficient of $X^{m-1}$ in $F$ vanishes by symmetry. In $u^2F-(uX-v)(F-G)$ the first two coefficients cancel. The next is $e=v^2-uw+u^2f_2$, the determinant of the four leading Sylvester rows for this principal subresultant. If $u=mt$ is invertible modulo $N$, division by $u^2$ gives the ordinary Euclidean remainder and preserves its coefficient gcd. Lean proves the following identity for all public integer shifts.

$$
576 e=m^2(m^2-1)Q_m(t),\qquad
Q_m(t)=48t^4-24(1+m^2)t^2+(m^2-1)^3.
$$

For a prime divisor $p>m+1$, away from $p=2,3$, the two sides have the same zero condition as $Q_m(t)$. If $\gcd(N,576m(m^2-1))=1$, the normalized probe has exactly the coefficient gcd even over the composite ring. After precomputing the width constants, one square, one multiplication by the variable $t^2$, fixed scalar operations and one gcd suffice per shift. The probe can run independently of computing the original block product. [Integer coefficient, determinant and root-count proofs](../PrimeFactors/BlockSubresultantProbe.lean) · [Implementation](../experiments/block_subresultant.py)

For width three the test reduces to $P(t)=3t^4-15t^2+32$, with $e=2P(t)$. At $t=5$ the block is 1 through 9, the first pivot is 15, and the next is 3064. Only the latter shares a divisor with $153583=383\cdot401$. At the prime 43 the four residues 11, 20, 23 and 32 all make the quartic zero while their nine entries remain units. A single affine test with invertible slope can cover only one residue there. For every fixed odd width and prime above three, the normalized quartic has at most four roots. For width three, $12P(t)=(6t^2-15)^2+159$. A prime at which $-159$ is a quadratic nonresidue can never be found by this probe. The root count describes shifts modulo one fixed prime. The choice $t=\lfloor\sqrt N\rfloor$ does not sample shifts uniformly. [Checked examples and four-root bound](../PrimeFactors/BlockSubresultantProbe.lean)

## Comparison on complete small populations

For every unordered pair of distinct $b$-bit primes with a $2b$-bit product, use $m=3$ and $t=\lfloor\sqrt N\rfloor$. After a unit block gcd, compare one quartic gcd to one gcd at the adjacent smaller integer $t-5$. Both receive the same products. Source prime pairs supply the population. Both searches see only $N$.

| Prime bits | Eligible pairs | Block finds one prime | Block gcd is $N$ | Unit block gcd | Further quartic splits | Further adjacent splits | Both |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 9 | 543 | 15 | 18 | 510 | 3 | 12 | 0 |
| 10 | 1,718 | 18 | 33 | 1,667 | 2 | 14 | 0 |
| 11 | 5,530 | 33 | 61 | 5,436 | 8 | 33 | 0 |

The adjacent check found more splits at every width. Its first nine-bit-panel success was $139093=367\cdot379$ at $t=372$, where the rectangle and quartic gave unit gcds and $t-5=367$. The benchmark retains a factor found by either check. The quartic found thirteen different pairs the adjacent check missed. A block gcd equal to $N$ is reported separately because isolating its entries would cost additional work. These results establish an inexpensive additional test and give no practical bound on the number of shifts needed for an arbitrary large product. Reproduce the counts with `python3 -m experiments.block_subresultant`. [Census](../experiments/block_subresultant.py)

On the independently generated 2048-bit control and the structured crossed control, all three gcds were one. The unrecovered cofactor in each run was the entire input. Each used one integer square root, nine rectangle positions and three gcds. In 501 repeated calls on the same machine, the median CPU times for the complete comparison were 193 μs and 85 μs respectively, excluding certificate generation. Those timings cover one shift. [Benchmark fixtures](../benchmarks/block-subresultant.json)
