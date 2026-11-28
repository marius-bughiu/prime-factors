# How much shorter can the count be if we allow two answers?

Allowing two possible corrections can shorten the count to the first **1/120 of the product**. The denominator 120 is the largest for which even one unit product residue admits at most two corrections across all its compatible unit pairs. With a single correction the largest denominator was 24. Both bounds concern the complete list before using any other information about the primes. [Two-correction upper bound](../PrimeFactors/FractionalTwoCorrectionLimit.lean) · [One-correction classification](../PrimeFactors/FractionalPrefixResidues.lean)

We selected 12,827 and 15,707 to realize the two corrections. Both leave remainder 107 on division by 120. In each case, exactly one positive integer through the cutoff shares a factor with the product. The two possible prime sums are $120+108=228$ and $120+132=252$. The first product has primes 101 and 127, with sum 228. The second has primes 113 and 139, with sum 252. Testing the discriminant against the actual product distinguishes the answers. In a direct scan, the first nonunit already supplies a factor. [Both examples and the 120-entry modulus](../PrimeFactors/FractionalTwoCorrectionObstructions.lean)

## Why the list has to grow

Let $N=pq$ for distinct primes, choose a denominator $m\ge2$ coprime to $N$, and write $C_m$ for the number of positive integers through $L=\lfloor N/m\rfloor$ that share a factor with $N$. The prime sum is $mC_m+r$, where $r$ is the **ordinary integer sum** of the two least residues of the primes modulo $m$. Let $K$ be the number of possible corrections obtained by ranging over all unit pairs with product $N\bmod m$. Counting them modulo $m$ can merge distinct corrections. Modulo four, for instance, product one gives ordinary sums two and six. Both reduce to two. [Earlier count formula](counting-a-fraction-of-the-residues.md) · [Coordinate sumsets of modular hyperbolas, Bower, Evans, Luo and Miller](https://arxiv.org/abs/1212.2930)

Any multiple of 20,160 can occur modulo $m$ as a difference between two compatible modular sums. There are $m/\gcd(m,20160)$ such residues. A list of $K$ ordinary corrections supplies at most $K(K-1)+1$ differences, including zero. Consequently

$$
\frac{m}{\gcd(m,20160)}\le K(K-1)+1,\qquad
N<20160\,K^2(L+1).
$$

When $K\le2$, the first inequality forces $m$ to divide 120,960. Every divisor of that number exceeding 120 has a divisor among 7, 27, 64, 45, 80 and 144. Each of those six smaller moduli forces at least three modular sums for **every** unit product. Compatible unit pairs at a divisor lift to unit pairs at $m$. This proves the upper bound of 120. At 120, the only qualifying unit product is 107. Combining the bound with the exhaustive census leaves 36 product-residue classes across 20 denominators from 2 through 120. At a prime denominator there is a simpler exact rule. For a given sum and product the two roots fix the unordered residue pair, hence $2K=m-1+\#\{x:x^2=N\bmod m\}$. [Spacing theorem](../PrimeFactors/UniversalSumStride.lean) · [Correction counts](../PrimeFactors/FractionalCorrectionBudget.lean) · [Finite obstructions](../PrimeFactors/FractionalTwoCorrectionObstructions.lean)

For a 2,048-bit input, either the prefix length or the full list exceeds $2^{677}$. At a prime denominator one of them exceeds $2^{1022}$. If the denominator reaches the square root, the full list alone exceeds $2^{504}$. These statements charge a literal scan or an exhaustive list. Information about the factor sizes can make a count free or narrow the list considerably. [Full-size bounds](../PrimeFactors/FractionalCorrectionBudget.lean)

| Denominator for 2,183 | Positions through the cutoff | Nonunits | Possible corrections before size checks |
| ---: | ---: | ---: | ---: |
| 24 | 90 | 3 | 1 |
| 48 | 45 | 1 | 3 |
| 120 | 18 | 0 | 4 |
| 240 | 9 | 0 | 8 |
| 257 | 8 | 0 | 128 |

The finite experiment checked 18,061 product-residue classes at denominators 2 through 240, 257 and 263. Across 12,536 small product/denominator combinations it used 374,525 gcds for the direct counts and tested 394,608 candidate sums. The separate table setup enumerated 2,113,545 ordered unit pairs. Combining several counts can still leave alternatives. The products 89,693 and 91,123 both give remainder 318 modulo 715 and counts 120, 54 and 45 at denominators 5, 11 and 13. The common list is exactly 604 and 606. The full product distinguishes them. [Experiment](../experiments/fractional_correction_menu.py) · [Counts, setup and controls](../benchmarks/fractional-correction-menu.json)

## When can the product give the count for free?

For $p<q<2p$, take $D=\lceil\sqrt N\rceil$. Then $p<D\le q<2D$, so $C_D=\lfloor p/D\rfloor+\lfloor q/D\rfloor=1$. Farther out, $m^2\ge2N$ implies $C_m=0$. At 2,183 the square-root cutoff denominator is 47. Moving to 48 still gives one, which can be confirmed by checking that 47 does not divide the product. Its three candidate sums are 72, 96 and 120. In this small example the ordinary balanced sum range and the product modulo four already select 96. [Free readings and comparison](../PrimeFactors/FractionalFreeReadings.lean)

Information about both candidate factors can reduce the list still further. Suppose their residues are positive, ordered as $x\le y<2x$, and their sum satisfies the necessary balanced bounds $4N\le(x+y)^2<9N/2$. Then $8N/9<xy<9N/8$. Once $8m\ge N$, a product congruent to $N$ modulo $m$ in this interval must equal $N$. For 12,827 at denominator 1,604, both 228 and 232 pass the sum bounds. The pair $(23,209)$ gives 232 and fails the balance check. The pair $(101,127)$ gives 228 and multiplies to the input. The constant is close to sharp even for distinct primes of known width. For $N=583{,}201=643\cdot907$ and $m=72{,}898$, the different ten-bit primes 809 and 811 also pass the balance tests and satisfy $809\cdot811=N+m$. Here $8m=N-17$. Identifying the surviving pair in a large implicit list is the remaining computational problem. [Bounds on lifts and prime-pair uniqueness](../PrimeFactors/FractionalBalancedLifts.lean)

## Reusing a gcd in an exact count

A positive integer has a unique factorization $ab$ in which every prime of $a$ divides a chosen wheel $W$ and $b$ is coprime to $W$. If $W$ is coprime to $N$, all positions with the same $b$ have the same gcd with $N$. Count each nonunit core $b$ with weight equal to the number of such multipliers $a\le L/b$. This counts every position once. [Weighted identity and number of cores](../PrimeFactors/FractionalPrefixWheel.lean)

At 2,183 and cutoff 90, the wheel 210 needs 20 core gcds and one eligibility gcd. Core 37 occurs twice, at 37 and 74. Core 59 occurs once. The implementation also made 101 multiplications to generate 43 smooth multipliers, two weight divisions and 86 weight comparisons. The reusable wheel table took 210 small gcds to construct. Stopping at the first hit took eight core gcds. Ascending balanced trial division found 37 in two divisions. For wheel 30, the proof gives an exact count of 23 nontrivial core checks on this example, and more than $2^{2040}$ on intervals longer than $2^{2042}$. [Census and cost breakdown](../benchmarks/fractional-prefix-wheel.json) · [Wheel implementation](../experiments/fractional_prefix_wheel.py)

Uniform sampling offers another comparison. For a one-correction denominator, write $S=p+q$. Scaling a uniformly sampled nonunit flag to estimate $S$ gives variance $V=(S-m)(p-1)(q-1)$. The ordinary sample mean based on $k$ independent draws has mean squared error $V/k$. For $L>1$, drawing $k$ distinct positions uniformly gives mean squared error $V(L-k)/(k(L-1))$. With a single available position, reading it gives the exact count. At 2,183 and $m=24$, RMS error below one needs 150,337 independent draws or all 90 distinct positions. The possible sums are multiples of 24. Even for the looser RMS target of 12, the thresholds are 1,045 and 83. RMS describes error across samples. A particular estimate can miss the correct multiple. [Exact errors, examples and full-width bounds](../PrimeFactors/FractionalPrefixSampleCost.lean)

## Why other slices can give the same count

When $m$ divides $N+1$ and $p+q$, each interval $(jN/m,(j+1)N/m]$ contains exactly $\varphi(N)/m$ integers coprime to $N$. At 2,183, all 24 slices contain 87. The first slice has 90 positions and each subsequent slice has 91. If instead we partition the integers 1 through $N-1$ into $m$ blocks of equal integer length, their nonunit counts are equal exactly when $m$ divides both $p-1$ and $q-1$. [Endpoints and both partition theorems](../PrimeFactors/FractionalTotientSlices.lean)

Lehmer studied counts of coprime integers in fractional intervals. Germain later characterized equal distribution using odd Dirichlet characters and used their nonvanishing at one in the proof. The pinned RH repository includes nonvanishing to the right of the critical line for the applicable characters. Our semiprime slice identities use elementary counting. They specify what an exact reading would reveal and leave the efficient evaluation of a specified large count open. [Lehmer](https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/distribution-of-totatives/A1B6054448396406512E4ECE51DC6ADD) · [Germain, Theorem 1.1](https://doi.org/10.4153/CMB-2005-019-9) · [Pinned RH statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)
