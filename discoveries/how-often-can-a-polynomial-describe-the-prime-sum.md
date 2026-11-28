# How often can a polynomial describe the prime sum?

Suppose someone proposes a fixed equation in the product $N$ and the unknown prime sum $S$. It can use addition, subtraction, multiplication and rational coefficients of any size. If the equation is a nonzero polynomial of degree at most $2^{128}$, it holds for **fewer than one in $2^{879}$** eligible 2,048-bit products. This bound is unconditional. It gives the equation credit whenever the actual sum is *one* of its solutions, however many false answers it may also admit. [Full-size population theorem](../PrimeFactors/PrimeSumPolynomialPopulation.lean)

## What happens with five small primes?

Choose 3, 5, 7, 11 and 13. They give ten products of two different primes. What is the largest number of those products on which **one quadratic equation** can describe the true sum? The exact answer is seven. Here is a quadratic that attains it.

$$ (N-3S+9)(N-5S+25)=0. $$

On substituting $N=pq$ and $S=p+q$, the first term becomes $(p-3)(q-3)$. The second becomes $(p-5)(q-5)$. The equation succeeds exactly on the pairs containing 3 or 5. At $55=5\cdot11$ it accepts the sum 16. At $143=11\cdot13$ it rejects the sum 24. The three misses are 77, 91 and 143. [Lean checks for the seven-of-ten bound and the two individual examples](../PrimeFactors/PrimeSumPolynomialExamples.lean)

For $n$ distinct possible primes and degree $d\le n-1$, the largest number of distinct products covered is

$$\binom n2-\binom{n-d}2.$$

To see why, fix one prime $p$. The equation in its partner $q$ now has degree at most $d$, so it has at most $d$ roots unless the whole row is zero. There can be at most $d$ such whole rows. Counting the pairs once gives the bound. Choosing any $d$ primes ahead of time and multiplying their linear equations reaches it. For $d<n-1$, every equation attaining the bound succeeds **exactly** on pairs containing one of its $d$ selected entries, even outside the original grid. At the endpoint, other equations can tie. For example, $S=3$ covers the sole distinct pair drawn from $\{1,2\}$ without containing a whole row. [Upper bound](../PrimeFactors/PrimeSumPolynomialExtremum.lean) · [Attaining the bound](../PrimeFactors/PrimeSumPolynomialStars.lean) · [Classification of equality](../PrimeFactors/PrimeSumPolynomialSaturation.lean)

The elementary symmetric polynomials $pq$ and $p+q$ satisfy no polynomial identity over all rational $p,q$. Substitution into a nonzero equation therefore preserves nonvanishing. A standard finite-grid root bound then applies, and the stronger count above takes account of the symmetry and excludes repeated factors. Finite-grid bounds with separate degree constraints have a substantial literature. [Checked substitution and Schwartz–Zippel bound](../PrimeFactors/PrimeSumPolynomialGrid.lean) · [Bishnoi, Clark, Potukuchi and Schmitt](https://arxiv.org/abs/1508.06020)

## What if we choose an equation after seeing the product?

Take a collection of equations chosen before the product arrives. The rule for selecting from that collection may use every bit of $N$. If the sum of their degrees is $D>0$, the fraction of eligible products on which **any** equation in the collection holds is below $D/2^{1007}$. In particular, a collection of $2^{32}$ equations of degree up to $2^{96}$ still covers fewer than one in $2^{879}$. The proof multiplies the equations together. The product vanishes wherever at least one entry vanishes. A rational prediction $S=A(N)/B(N)$ is included by clearing its denominator at inputs where $B(N)\ne0$. [Product-dependent selection and rational graphs](../PrimeFactors/PrimeSumPolynomialMenu.lean)

Here an eligible product has two distinct 1,024-bit primes and itself has 2,048 bits. The count includes every such pair once. The proof first gives an upper bound for the ordered grid of all 1,024-bit primes, then uses an unconditional bound on how many pairs have a full-width product. No Riemann-hypothesis estimate enters this comparison. [Population proof](../PrimeFactors/PrimeSumPolynomialPopulation.lean) · [Normalization](../PrimeFactors/SquareRootPhasePopulation.lean)

## Does predicting a neighborhood of the sum help?

Give an integer polynomial $P(N)$ credit if the true $S$ falls within $2^{128}$ of its answer. Even with that tolerance, any such polynomial of degree at most $2^{32}$ succeeds on fewer than one in $2^{845}$ eligible products. Each possible integer error $j$ contributes one equation $S-P(N)-j=0$. For the toy prediction $20\pm2$, the true sums for 77 and 85 land on opposite endpoints, while 143 falls outside the window. [Window theorem and endpoint controls](../PrimeFactors/PrimeSumPolynomialWindow.lean)

These bounds have specific hypotheses. A congruence tests equality in a finite ring. A floor introduces inequalities. The familiar condition $S^2-4N=g^2$ introduces a third unknown, the prime gap $g$. Each needs a separate argument. On a selected 39-bit product, thirteen modular tests actually reduced 7,273 candidate sums to one. The degree bounds here concern exact equations in two rational variables. [Integer square-witness equivalence](../PrimeFactors/FactorSum.lean) · [Checked modular example](../PrimeFactors/PublicSumSieveControl.lean)

## Does an equation in the ratio of the primes work better?

The quantity $T=S^2/N$ depends only on the ratio of the primes. For two distinct primes its reduced denominator is exactly $N$. For example, $7$ and $11$ give $324/77$, a fraction already in lowest terms. No other sorted prime pair anywhere has that value. If an integer polynomial vanishes at $T$, the rational-root theorem forces its leading coefficient to be divisible by $N$. A monic integer polynomial therefore cannot vanish at this ratio for even one such pair. [Denominator and rational-root proofs](../PrimeFactors/PrimeSumRatioRoots.lean)

More generally, ask for equations unchanged up to an overall factor when both primes are rescaled. Such an equation has the same weight $2i+j$ for every term $N^i S^j$. A nonzero equation of this kind and total degree $d$ holds for at most **$\lfloor d/2\rfloor$ distinct semiprimes across all prime sizes**. Dividing out the common scale leaves a polynomial in $T$ of degree at most $\lfloor d/2\rfloor$. Each rational root identifies at most one prime pair. The limit is exact. For any $k$ selected pairs, multiplying their $k$ equations $S^2-T_iN=0$ gives degree $2k$ and those exact $k$ hits. [Global bound and matching constructions](../PrimeFactors/PrimeSumHomogeneousGrid.lean)
