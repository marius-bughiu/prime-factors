# How often can two weighted remainders split a large product?

Even if someone could pick the best two weights and search positions for each input for free, this method would still miss almost every ordinary 2,048-bit product. Let each weight be any positive integer up to $2^{128}$. For each weight allow the first $2^{128}$ positions in its search. **Fewer than one in $2^{229}$ eligible prime pairs has any choice that yields a factor.** This includes choices made after seeing every digit of the product. Lean checks the result for the actual integer square test and gcd. [Target theorem](../PrimeFactors/WeightedMultiplierLabels.lean) · [The exceptional constructed 2,048-bit success](factoring-with-two-weighted-square-tests.md#a-constructed-2048-bit-example)

The population consists of distinct 1,024-bit primes $p<q$ drawn uniformly among pairs with $N=pq$ of 2,048 bits. For each weight $r$, start at the first integer $A\ge2\sqrt{rN}$ congruent to $r+N$ modulo $\gcd(24,2(r+N))$. Later positions add this same stride. Choose another label $B$ at weight $s$, and set $D=A^2-4rN$, $E=B^2-4sN$. A success requires a square $DE=z^2$ and a proper divisor $\gcd(AB-z,N)$. Individual square tests, relations involving more rows, and other ways of combining them have different success conditions. The earlier result for a single multiplier allows its first midpoint to be anywhere in a wider interval. [Single-multiplier theorem](square-collision-density.md)

| Largest weight | Positions per weight | Upper bound on fraction of products reached |
|---:|---:|---:|
| $2^4$ | 1 | $2^{-727}$ |
| $2^{16}$ | $2^{16}$ | $2^{-674}$ |
| $2^{64}$ | $2^{64}$ | $2^{-483}$ |
| $2^{128}$ | $2^{128}$ | $2^{-229}$ |
| $2^{160}$ | $2^{64}$ | $2^{-216}$ |
| $2^{64}$ | $2^{256}$ | $2^{-255}$ |

## Counting the products that could work

For fixed $r,s,A,B$ the integer $C=|sA^2-rB^2|$ is public. If $C=0$, a square match gives the whole input as its difference gcd. Otherwise, write $rs=tf^2$ with $t$ squarefree. A match supplies a point on the following equation:
$$x=sD+rE,\qquad y=2fz,\qquad x^2-ty^2=C^2.$$
Knowing $x$ determines $N$ exactly because $8rsN=sA^2+rB^2-x$. Now it is enough to bound the number of integer points at the available height. The proof includes equal weights, weights sharing large factors and $t=1$. [Identities and the zero case](../PrimeFactors/WeightedMultiplierPell.lean) · [Injection from inputs](../PrimeFactors/WeightedMultiplierFiber.lean)

Divide $x,y$ by their gcd $g$, which divides $C$, and put $m=C/g$. The primitive point selects a square root of $t$ modulo $m^2$ by dividing its first coordinate by its second in that residue ring. The modulus-one case contributes one class. Each root is a unit because $t$ is squarefree. Dividing by any one chosen root therefore maps the entire set of roots into the unit square roots of one. The Chinese remainder theorem and the dyadic root bound give at most $2\cdot2^{\omega(m)}$ classes. Summing $2^{\omega(m)}$ over divisors $m$ of $C$ gives $\tau(C^2)$. [Root count and exact divisor sum](../PrimeFactors/WeightedMultiplierRoots.lean)

Two different primitive points in one class have an integral quotient of norm one. In order of increasing positive first coordinate, the next first coordinate is at least twice the preceding one. Since $x<2^{2048}$ for the six stated budgets, each class has at most 2,048 points. Altogether at most $4096\tau(C^2)$ different products can work at any fixed tuple. The proof counts actual integer points, with no assumption about how frequently they occur. [Separation and finite class count](../PrimeFactors/WeightedMultiplierPoints.lean)

Finally put $X=2^{1023}$ and suppose the largest weight is $K=R^2$ and there are $J$ labels per row. For fixed $r,s$, the number of possible pairs of label values across *all* these inputs is at most $197RXJ$. There are about $\sqrt r\,X$ possible first labels, while fixing one first label confines the second to an interval of length at most $24(1+\sqrt{s/r})J$. Keeping the same first weight in both estimates gives the factor $R$. The height bound $C<256KRXJ$, the uniform divisor estimate and the count of eligible prime pairs give the six numbers above. Assigning one witness to each successful product allows arbitrary input dependence. [Geometry and constants](../PrimeFactors/WeightedMultiplierPopulation.lean) · [Counting the actual prime pairs](../PrimeFactors/WeightedMultiplierCoverage.lean)

## Can a few weights help on smaller numbers?

For $137{,}549{,}339$ the first labels at weights 2 and 6 give excesses 53,217 and 122,713. Their product is $80{,}811^2$, and the gcd gives 8,693, with cofactor 15,823. The first 17 individual labels at each of the eight weights all miss. Filtering the individual tests lets us reach another successful label after just two further exact square tests. Lean verifies the factors. [Reproducible fixture](../benchmarks/weighted-square-menu.json)

We compared three ways to spend up to 120 more integer square tests after checking the first two labels at each of weights 1 through 8. The ordinary search spends them on later single labels. The paired search tries all pairs of the first 16. A combined search uses small-prime residue tests to reject impossible pairs, then spends its remaining square tests on later single labels. A fourth comparison applies the same local tests to *single* labels, allowing up to 4,096 labels to find 120 that pass. Each search stops on finding a proper factor. [Algorithms and budgets](../experiments/weighted_pair_hybrid.py)

| Inputs | Ordinary single labels | Pairs | Combined search | Sieved single labels |
|---|---:|---:|---:|---:|
| All 228,713 eligible products of 14-bit primes | 172,516 | 67,639 | 172,737 | 228,713 |
| 8,192 fresh products of 16-bit primes | 3,442 | 1,219 | 3,440 | 8,192 |
| Eight ordinary 80-bit products | 0 | 0 | 0 | 0 |
| Two ordinary 2,048-bit controls | 0 | 0 | 0 | 0 |

On the complete 14-bit-prime census the combined search gained 396 answers the ordinary search missed and lost 175 others. That small net gain disappeared on the fresh sample. The sieved single search found every product in both smaller populations. It did more work to achieve that coverage. On the full census it took 11.29 seconds, compared with 4.26 seconds for ordinary single labels and 6.67 seconds for the combined search. On the fresh sample it screened 2,758,740 additional labels to perform 81,653 additional exact roots. Paired roots can have roughly twice the operand width of single roots. The published resource counts include sieve arithmetic and gcds; individual timings describe the measured run. The census checks discovered divisors against independently generated primes. The highlighted factorizations also have Lean certificates. [Work counts and independent draw](../research/weighted-pair-hybrid.json) · [Early-stop timings](../research/weighted-pair-hybrid-timing.json) · [Complete matched-label comparison](../research/weighted-pair-menu.json)
