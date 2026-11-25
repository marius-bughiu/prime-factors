# Can a Dedekind sum rank factor remainders?

A classical Dedekind sum gives a fast, exact rational score for a proposed factor remainder $a$ using the whole product $N$. For every 2,048-bit product of two 1,024-bit primes, **the scores put all positive candidates through $2^{682}$ in exactly the same order on every input**. The greatest score belongs to 1, the next to 2, and so on. Restricting to odd remainders preserves their numerical order. In particular, ranking the candidates this way gives no guidance on which of the positive quartic searches modulo $2^{610}$ to try first. The result concerns the raw scores of the individual representatives. [Lean proof](../PrimeFactors/DedekindLaneRanking.lean) · [Positive quartic search](chebyshev-quartic-window.md)

## Why the full-product score has a predetermined order

Write $S(a,N)=12s(a,N)$ for the normalized classical Dedekind sum, with $\gcd(a,N)=1$. The sawtooth definition is a sum of $N$ terms. Periodicity and Dedekind reciprocity evaluate it along the Euclidean algorithm, starting from modulus one. In particular,

$$S(a,N)=N/a-3+a/N+1/(aN)-S(N\bmod a,a).$$

Girstmair studied large values over all numerators, including candidates far from zero, and gives the classical reciprocity identity and explicit bounds on its error term. The question here compares two candidates in the small initial interval and asks precisely how far the sorting guarantee extends. [Girstmair, *The largest values of Dedekind sums*, equations (2), (3), and (8)](https://arxiv.org/pdf/1607.07682)

For $1\le a<b\le B<N$, the ordering $S(a,N)>S(b,N)$ holds whenever $(b-a)N\ge2B^3$. To see this, the leading difference $N/a-N/b$ is at least $2B$. Each small correction $a/N+1/(aN)$ lies in $[0,2]$. The two reciprocity remainders have absolute values at most $a-1$ and $b-1$. After subtracting these possible errors the difference is at least $2B-a-b>0$. Lean proves the remainder bound $|S(r,m)|\le m-1$ by induction on the Euclidean evaluation. The identification of that evaluation with the classical sawtooth sum uses published reciprocity. [Comparison and remainder proofs](../PrimeFactors/DedekindLaneRanking.lean)

For all candidates take $2B^3\le N$. At the full target width, $2(2^{682})^3=2^{2047}\le N$, and every candidate in this range is smaller than either prime and hence a unit. For **odd** candidates the gap is at least two, so $B^3\le N$ suffices. In this full-size range every score is positive: already $N\ge a(a+2)$ suffices in the reciprocity formula. The sawtooth sum changes sign at $-a$, so ranking signed candidate magnitudes gives the identical order up to sign. There is also a permutation interpretation. Multiplication by $a$ permutes the residues modulo $N$. Its inversion count is $[(N-1)(N-2)-NS(a,N)]/4$, so ranking by exact inversion count gives the reverse score ordering throughout the same interval. [Chen, Dunn, Hewett and Silas, equation (1.4)](https://arxiv.org/pdf/1411.4092#page=2)

## The cubic threshold is sharp

For odd $a\ge7$ choose $b=a+2$ and $N=ab(a-6)+a+1$. Both candidates are coprime to $N$. The two reciprocal numerators are $1\bmod a$ and $-1\bmod b$. Substituting $S(1,k)=k-3+2/k$ and $S(-1,k)=-S(1,k)$ gives

$$S(a,N)-S(b,N)=-8-\frac1a-\frac1b-\frac2N\left(1-\frac1{ab}\right)<-8.$$

Here $N/b^3$ tends to 1 from below. Thus replacing the odd-candidate condition $N\ge B^3$ by $N\ge cB^3$ for a fixed $c<1$ fails on arbitrarily large odd inputs. The family makes no promise about its factorization. A concrete balanced semiprime also reverses the order. At $a=815$, $b=817$ and $N=538677511=21727\cdot24793$, the ratio $N/b^3$ exceeds $0.9877$. The product has 30 bits and each prime has 15. Lean checks the general reversal, the product and both primes. [Boundary family and certified example](../PrimeFactors/DedekindLaneRanking.lean)

## What if a selector reads the low bits instead?

Put $D=aS(N\bmod a,a)$. This is an integer. In fact Euclidean reciprocity gives the two assertions $d=mS(r,m)\in\mathbb Z$ and $rd\equiv r^2+1\bmod m$ simultaneously by induction for coprime inputs. When $a^2+1<N$, the reciprocity formula becomes

$$aS(a,N)=N-3a-D+(a^2+1)/N,\qquad
\lfloor S(a,N)\rfloor=\left\lfloor\frac{N-3a-D}{a}\right\rfloor.$$

Consequently the lowest $t$ bits of $\lfloor S(a,N)\rfloor$ are entirely determined by $N\bmod (2^t a)$. Replacing $N$ by another admissible $N'$ in that residue class fixes $D$ and changes the displayed floor by a multiple of $2^t$. Adaptive queries to such bits therefore fit the earlier pathwise least-common-multiple bound after charging the modulus $2^t a$ for each query. Magnitudes, combinations of different scores, and further arithmetic on the whole product require their own analysis. The order and integer-part identities hold unconditionally, so the pinned Dirichlet RH statement cannot change the ranking. [Lean numerator and floor proofs](../PrimeFactors/DedekindLaneRanking.lean) · [Adaptive whole-product residues](adaptive-whole-product-residues.md) · [Pinned RH statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)

The same periodicity holds for the integer numerator $d=NS(a,N)$ modulo any $P$, for every $a<N$. Indeed $ad=N^2+a^2+1-3aN-ND$. When $N$ changes by a multiple of $aP$, its right side changes by a multiple of $aP$. In particular the lowest $t$ bits of the inversion count require only $N\bmod(2^{t+2}a)$. The inverse congruence for $d$ also gives $\gcd(d,N)=\gcd(a^2+1,N)$. Extracting a factor from this denominator cancellation is already the elementary gcd test on $a^2+1$. [Lean numerator periodicity](../PrimeFactors/DedekindLaneRanking.lean) · [Girstmair, fractional-part identity (1)](https://arxiv.org/pdf/1310.1253#page=2)

For scale, take $X=2^{1023}$ and $R=2^{614}$. Sample uniform distinct unordered primes in $[X,2X)$ conditional on a full 2,048-bit product. A selector whose only input is the sort order chooses a fixed set of at most $T$ guesses. Allow either factor and either sign for every guess. One residue contains fewer than $4X/(R\log(X/R))$ primes by Brun–Titchmarsh since $\varphi(R)=R/2$. For any such first prime the interval has fewer than $1.511X/\log X$ possible partners. The conditioned population has more than $(0.22X/\log X)^2/2$ pairs. After allowing $2T$ signed possibilities, success is below

$$\frac{16(1.511)}{0.22^2}\,\frac{1023}{409}\,\frac{T}{R}<2^{11}\frac{T}{R}.$$

In particular even $2^{40}$ such guesses cover less than a $2^{-563}$ fraction. This probability bound is a paper deduction from the published prime-counting estimates. The ordering itself holds pointwise for every target product. [Montgomery and Vaughan, Theorem 2](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf#page=3) · [Exact prime-population bounds](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)
