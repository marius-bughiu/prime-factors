# What can the early continued fractions tell us?

The ordinary continued fraction of the square root of a product gives a square congruence at every step. On two independently sampled products already in the project, joining early congruences recovered the primes after 767 and 5,138 steps. On the existing 2,048-bit test, all 65,536 congruences from the previously attempted walk have a different obstruction. We checked that no nonempty subset of them has a square product, even after allowing every prime up to 16,777,216 as a correction. These are results about the specified prefixes of three products. [Checked benchmark cases](../benchmarks/pell-relations.json) · [Earlier midpoint search](pell-multiplier-pairs.md)

## Checking a whole collection at once

Take an odd semiprime $N=pq$ and a public multiplier $m$ with $mN$ nonsquare. The complete denominators $Q_i>0$ and preceding convergent numerators $A_i$ of $\sqrt{mN}$ satisfy

$$
 A_i^2\equiv R_i\pmod N,\qquad R_i=(-1)^i Q_i,\qquad i=1,2,\ldots.
$$

Keep $A_i$ only modulo $N$, check the identity on every row, and test $\gcd(Q_i,N)$. A proper gcd gives a divisor immediately. Use the rows with unit denominators in the following calculation. Gathering such relations and multiplying them until the right side is an integer square is classical continued-fraction factorization. The earlier midpoint search in this project kept only the central denominators. [Morrison and Brillhart, *A method of factoring and the factorization of F₇*](https://doi.org/10.1090/S0025-5718-1975-0371800-5) · [Lenstra and Manasse on relation spaces and cycles](https://infoscience.epfl.ch/server/api/core/bitstreams/490ebcc2-36fb-4a5a-80fa-6a8e6f0831fe/content)

For each $v_i=|R_i|$, remove every prime power whose prime occurs in any other row, leaving a **private part** $u_i$. If $P$ is the product of all the $v_i$, the value $(P\bmod v_i^2)/v_i$ gives the other entries' product modulo $v_i$. Compute every such remainder with a product and remainder tree. Take the gcd with $v_i$ and divide out all powers supported on that gcd. A nonsquare $u_i$ rules out this row in every square-producing subset. It is coprime both to $v_i/u_i$ and to all other rows, and coprime positive integers must each be squares if their product is square. Removing all such rows can disclose more private parts, so repeat until the set stops changing. [Lean leaf identity and private-cofactor theorem](../PrimeFactors/PellCycles.lean) · [Bernstein on factors shared between integers](https://cr.yp.to/lineartime/multapps-20080503.pdf)

On the remaining rows, split any two distinct overlapping bases $a,b$ into $g,a/g,b/g$, with $g=\gcd(a,b)>1$. Drop ones and duplicates. The product of the distinct bases decreases, and every old integer remains a product over the new bases. This gives a pairwise coprime basis whose elements may be composite. For each nonsquare basis element, keep the parity of its exponent in each row. Also keep the sign as one parity bit. A subset has a positive square product exactly when all these bit sums are even. Indeed a square product over coprime bases requires each base power to be a square, and an odd power of a nonsquare base stays nonsquare. Binary elimination now gives a basis for the entire space of square dependencies. The small reference implementation uses repeated pairwise gcds on surviving rows. Bernstein gives a substantially faster general factor-refinement algorithm. [Lean coprime-basis criterion](../PrimeFactors/PellCycles.lean) · [Bernstein, *Factoring into coprimes in essentially linear time*](https://doi.org/10.1016/j.jalgor.2004.04.009)

For a dependency $S$, set $X_S=\prod_{i\in S}A_i\bmod N$ and $Y_S=\sqrt{\prod_{i\in S} R_i}>0$. If $X_S\not\equiv\pm Y_S\pmod N$, then $\gcd(X_S-Y_S,N)$ splits $N$. At each of its two odd prime factors, $X_S$ is congruent to either $Y_S$ or $-Y_S$. To check *every* dependency it suffices to test a basis. In a symmetric difference $S\mathbin{\triangle}T$, the repeated rows contribute $\prod_{i\in S\cap T}R_i$ on the $X$ side and its absolute value on the $Y$ side. These are the same unit up to sign. Therefore the symmetric difference of two trivial dependencies remains trivial, including when the overlap contains a negative norm. [Lean cancellation lemma and early numerical witness](../PrimeFactors/PellCycles.lean)

## Where the first useful row appeared

The following are the first splitting prefixes of the unmultiplied ordinary walk. In each case, the preceding prefix contained square dependencies and every one gave only the trivial sign. The column counting dependencies gives the dimension over the two-element field. A dimension of 23, for example, accounts for $2^{23}$ subsets including the empty set. The successful prefix can require more wall time than a particular earlier factor search. Continued-fraction updates do not count the gcd trees, matrix work, or final verification. [Bounded research implementation](../experiments/pell_relations.py) · [Fixtures including capped results](../benchmarks/pell-relations.json) · [Origin of the 63- and 79-bit inputs](../benchmarks/wide-modulus.json)

| Product | First splitting step | Dependencies one step earlier | Rows in the successful subset | Prime factors |
| --- | ---: | ---: | ---: | --- |
| 21,490,481 | 30 | 6 | 4 | 4,421 × 4,861 |
| 8,745,712,257,892,974,589 | 767 | 11 | 21 | 2,640,906,143 × 3,311,633,123 |
| 367,722,817,904,017,001,243,509 | 5,138 | 23 | 53 | 605,056,390,957 × 607,749,663,337 |

On the first input the selected rows are 6, 8, 14 and 30. Their positive norms are 5,525, 3,341, 4,112 and 2,057. Their product is $12{,}495{,}340^2$ and the four numerators multiply to 5,709,105 modulo the input. The gcd of their difference with the input is 4,421.

## What 65,536 rows rule out at full width

For the 2,048-bit input previously tried with $m=7\cdot19=133$, every one of the first 65,536 rows has a nonsquare private part. The smallest such part has 932 bits. The parity obstruction excludes all $2^{65536}-1$ nonempty subsets at once. This is a case-specific computation of gcds and square tests using a kernel-checked general implication.

We also allowed arbitrary extra factors supported on primes through $B=2^{24}$. Form $E$ as the product of all primes up to $B$ and start the remainder tree with $EP$. This removes every prime dividing $E$ from each private part. All 65,536 rows again had a nonsquare private part on this first pass, the smallest now having 902 bits. Thus for every nonempty subset $S$ and every positive $M$ whose prime factors are all at most $2^{24}$, the integer $M\prod_{i\in S}|R_i|$ is nonsquare. Indeed $M$ divides a power of $E$ and the private nonsquare in any selected row is coprime to $M$ and to everything multiplying it. Later rows, different multipliers and methods extracting other information from these residues remain open. The computation establishes a limitation of this specific walk on this input. [Lean theorem for unrestricted smooth corrections](../PrimeFactors/PellCycles.lean)

The complete strengthened check took about 11 seconds in a local run with Python 3.14 and gmpy2 2.3.2. It uses the product and the three public parameters above. For $r$ rows with total bit length $L$, the stored product tree occupies $O(L\log(2r))$ bits plus integer object overhead, and the remainder calculation also operates on integers as wide as the root product and the supplied prime product. The strengthened run constructs a 24,197,143-bit prime product. The cost of acquiring enough useful rows on a large input remains open. A 1,024-row version runs in CI with only the Python standard library. The following example selects the recorded input by its fixture ID.

```sh
python3 experiments/pell_relations.py 21490481 --max-steps 30
n=$(python3 -c 'import json; print(next(c["n"] for c in json.load(open("benchmarks/pell-pairs.json")) if c["id"] == "pell-2048-cap"))')
python3 experiments/pell_relations.py "$n" --multiplier 133 --max-steps 65536 --gmp --external-smooth 16777216
```
