# Can choosing a small fraction reveal the two primes?

We constructed a 2,048-bit product on which the number 49 leads directly to both prime factors. On a second product of the same size, we proved that **every** working pair of fractions has a smaller member of at least 2,031 bits, measured by multiplying the absolute numerator by the denominator. The gap between these examples comes from the arithmetic of the primes. Choosing the starting point after inspecting the product cannot change these thresholds. [Constructed input](planted-pair-fixture.md) · [Full-size lower and upper certificates](../PrimeFactors/EuclideanHeightExample.lean)

## What a small fraction says about the primes

The input is an odd product $N=pq$ of two distinct primes. A reduced fraction $a/b$ with $b>0$ represents a unit residue $r$ when $a\equiv br\pmod N$. Call $|a|b$ its height. We seek two distinct fractions representing the same $r$, both of height below $N/2$, whose signed numerator-denominator products multiply to a square. Every such pair reveals a proper factor. We allow any unit $r$, including one computed from every digit of $N$. Assume that at least one of the *two fractions used in the pair* has height at most $S$. A third unused fraction of low height makes no such promise. [Why every qualifying pair splits](same-source-pairs.md)

Order the positive cross products and divide them by their gcd $g$. The resulting numbers are coprime squares $u^2>v^2>0$. Since the original cross products are congruent and invertible modulo $N$, we have $u^2=v^2+hN$ for some integer $h\ge1$. The product of the two row heights is $g^2u^2v^2<SN/2$. Consequently
$$
2g^2 h v^2<S,\qquad (u-v)(u+v)=hN .
$$
The two primes divide opposite signs because each sign is positive and below $N$ and their product is a multiple of $N$. More explicitly, if both primes divided one sign then their product would divide that sign. Thus $u+v,u-v$ equal $ip,jq$ in some order for positive $i,j$ with $ij=h$. We get a condition directly on the unknown primes,
$$
ij(ip-jq)^2<2S .
$$
The determinant of two consecutive Euclidean vectors has absolute value $N$. Their numerator signs alternate, so a positive square pair needs nonadjacent rows. For rows separated by one intermediate vector, the absolute determinant is the intermediate Euclidean quotient times $N$. In general $h$ is the absolute determinant divided by $gN$. [Lean proofs of normalization, weights and bounds](../PrimeFactors/PairDeterminant.lean)

Let $K=\lfloor(S-1)/2\rfloor$ for an integral $S<N/2$. All candidates satisfy $1\le h\le K$ and $1\le v^2\le K/h$. For a fixed $h$ try each integer square strictly above $hN$ through $hN+\lfloor K/h\rfloor$. If the excess is $v^2$, try $\gcd(u-v,N)$. When $S^2\le16N$, at most the first square above each multiple can work. Larger budgets may require subsequent squares. For $527=17\cdot31$ with $S=112$, the gap at $23^2$ is 2 and the gap at $24^2$ is $7^2$, recovering both factors. This search takes only $N$ and the budget. It tests a superset of the possible fraction pairs and can find a factor before any qualifying pair exists at that budget. Searching multiples by differences of squares goes back to Lawrence and Lehman. The bound above relates the required multipliers and gaps to the chosen fraction height. [Search and controls](../experiments/guided_pairs.py) · [Hittmeir on Lawrence–Lehman search](https://arxiv.org/abs/2006.16729)

There is an exact converse if the normalized roots $u,v$ have already been found. Put $W=uv$. A pair with one height at most $S$ exists for this ratio exactly when there is a divisor $t$ of $W^2$ with $2W^2/N<t<N/2$ and $t\le S$. Split $t=AB$ with $A\mid u^2$, $B\mid v^2$. The fractions $A/B$ and $(v^2/B)/(u^2/A)$ have heights $t,W^2/t$, represent the same unit and have square norm product. Conversely, extracting the common numerator and denominator gcds leaves both heights divided by the same $g$ and their product becomes $W^2$. This yields the required $t$ from the originally bounded row. Constraining the common residue itself to be a square can increase the least possible maximum height. [Exact square-source criterion and small census](mixed-ratio-heights.md)

## How many products can have such a clue?

Choose distinct primes uniformly from $[X,2X)$ with $X=2^{1023}$, conditional on their product having 2,048 bits. The table bounds the fraction of these products for which even one suitable pair exists at any unit. It applies to searches spending arbitrarily many trials and to choices of clues informed by the entire input.

| Maximum height $S$ of at least one of the two rows | Upper bound on the fraction of inputs |
|---|---:|
| $2^{48}$ | $2^{-975}$ |
| $2^{1024}$ | $2^{-483}$ |
| $2^{1940}$ | $2^{-24}$ |

Here is an elementary numerator count. For the three thresholds, $S\le N/4$. Fix the smaller prime $p$. With $i,j$ assigned as above, $t=ip-jq$ is nonzero and $|t|<\sqrt{2S/(ij)}<p$ because $q<2p$. Thus $j\le i\le2j$, $j<\sqrt S<p$ and $|t|<2\sqrt S/j$. For fixed $j$ and signed $t$, the congruence $ip\equiv t\pmod j$ determines $i$ modulo $j$. Even the wider range $j/2<i<4j$ permits at most four such $i$. Each determines $q$ exactly. There are at most $4\sqrt S/j$ choices of the nonzero signed $t$. Summing gives at most $16\sqrt S(1+\log\sqrt S)$ possible partners per $p$, even counting composites.

For the denominator let $P$ count primes in $[X,2X)$ and $P_*$ primes in $[\sqrt{2}X,2X)$. The target population has at least $P_*(P_*-1)/2$ unordered prime pairs. Rosser–Schoenfeld give $P<1.511X/\log X$ and $P_*-1>0.22X/\log X$ at this width. Multiplying the partner bound by $P$ and dividing by the population lower bound gives each entry using rational arithmetic and $\log X<710$. This is a counting argument on paper with checked numerical inequalities. It needs no hypothesis on the distribution of the chosen residues. [Derivation of prime-population constants](stride-budget.md) · [Rosser and Schoenfeld, Corollary 1](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6) · [Executable bounds](../experiments/guided_pairs.py)

## A certificate for an individual product

For the crossed control used in earlier experiments we already have separately certified prime labels. They let us construct the root $z$ that equals $1$ modulo one prime and $-1$ modulo the other. Its negative is the other mixed root. Every candidate $u/v$ above represents one of these two, so it suffices to lower-bound $v|vz-kN|$ for every integer $k$ and $1\le v<N$. A Euclidean computation supplies a bound for all these denominators at once. At consecutive denominators $b,c$, write a lattice vector using integer coefficients $i,j$ as $(ib+jc,iR-jT)$ with $R,T\ge0$. For $0<ib+jc<c$ the coefficients cannot both be positive or both negative, and $i\ne0$. The absolute remainder is at least $R$. On $[b,c)$ the height is at least $bR$. The Lean checker verifies the change of basis at every step and the final denominator limit. [General checker](../PrimeFactors/EuclideanHeight.lean)

On this control the 1,134-step check gives the exact minimum $W$ of the mixed-root height. Every qualifying fraction pair has smaller height strictly above $2W^2/N$. The certificate also exhibits a pair at height $W/213$ by transferring the known divisor 213 between the two fractions. The upper bound exceeds the lower bound by less than 2%. They have the same bit length, **2,031**. This certifies the minimum bit length for the smaller row over all starting residues. The supplied primes are used for this individual certificate. Searching for a factor from the product alone has a separate benchmark. [Kernel-checked thresholds and attaining examples](../PrimeFactors/EuclideanHeightExample.lean) · [Reproduce the certificate](../experiments/seed_height_certificate.py) · [Product-only comparisons](sieving-small-factor-gaps.md)
