# Which prime rejects a wrong factor sum?

Suppose you know the product of two 1,024-bit primes. For each proposed sum, you can ask whether two remainders add to the sum and multiply to the product modulo a small prime. The true sum always passes. **Every other sum in the range below fails at some odd prime at most $2^{940}$.** This conclusion follows from published unconditional inequalities. Lean checks the deduction with the three inequalities supplied as hypotheses. [Exact theorem and hypotheses](../PrimeFactors/DiscriminantPrimeSeparation.lean)

The cost puts the result in perspective. There are **more than $2^{930}$ odd primes** in the family. Checking a proposed sum takes just one integer square root if you use the original product directly. The advantage of the remainder formulation is that many sums can share one table of allowed remainders. We have no efficient way to use these tables to locate the surviving sum over the full range. [Prime-count certificate](../PrimeFactors/DiscriminantPrimeSeparation.lean) · [Earlier small-table measurements](how-far-public-remainders-narrow-the-sum.md)

## Which sums does this cover?

Write $N=pq$. The candidate $s$ is a natural number with $4N\le s^2$, $s<N+1$ and $s<2^{1025}$. All three bounds use public information. The actual sum meets them when both primes have 1,024 bits. The first bound lets us take a real square root. The second excludes the factor pair $1,N$. The third uses the factor widths. For $s=p+q$ the discriminant $D=s^2-4N$ is $(q-p)^2$. Conversely, an integer square discriminant in this range gives the two integer factors $(s\pm\sqrt D)/2$. This includes the case of equal primes. [Integer proof](../PrimeFactors/Isolation.lean)

| Public remainder tests | What follows | What the proof uses |
| --- | --- | --- |
| Odd primes through $2^{520}$ | At most $2^{519}$ candidates in the full interval of $2^{1024}$ sums | Elementary larger-sieve bound checked in Lean |
| Odd primes through $2^{940}$ | Exactly one candidate after the public bounds above | Three published inequalities plus the Lean deduction |
| Odd primes below three million | Exactly one candidate in the earlier balanced interval | A separate paper deduction assuming Dirichlet GRH |

The last line assumes the generalized Riemann hypothesis for Dirichlet L-functions. The middle line uses neither that hypothesis nor the ordinary Riemann hypothesis. The cutoff bounds where a rejecting prime must exist for *each* wrong sum. Different sums can have different witnesses. [Larger-sieve proof](how-far-public-remainders-narrow-the-sum.md#what-can-be-proved-for-every-full-size-product) · [Earlier GRH argument and interval](factor-sum-residues.md#a-uniform-set-of-primes-that-isolates-the-sum)

## A wrong sum that passes modulo three

Take $9{,}523=89\times107$. Its true sum is 196. The guess 200 has the right parity and gives $D=200^2-4\times9523=1908=53\times6^2$. Modulo three, 53 leaves remainder two, which is a nonsquare. But 1908 leaves zero, so this test accepts the original guess. Modulo five the remainder is three, and the test rejects 200. The test modulo 27 also rejects it. [Checked arithmetic](../PrimeFactors/DiscriminantPrimeSeparation.lean)

In general, suppose $d$ is a nonsquare modulo an odd prime $\ell$, and $x\ne0$ contains exactly $a$ copies of $\ell$. Then $dx^2$ looks square modulo every $\ell^k$ with $k\le 2a$. Its first rejection comes at $k=2a+1$. In the example, the extra six contains one copy of three, so the first rejecting power of three is $3^3=27$. This explains why a witness for the squarefree part alone can misidentify which prime test rejects the original number. [Prime-power proof and the corresponding result at two](../PrimeFactors/MaskedSquareWitness.lean)

## Can pairs of tests tell us which interval to search?

Try dividing the range into short intervals. We would like to discard an interval as soon as we know it contains no common survivor. On $34{,}387=137\times251$, the first three candidate sums allowed by the balanced bounds and modulo four are 372, 376 and 380. Here is what the three public prime tests say. [Complete table and interval bounds](../PrimeFactors/PairwiseSumObstruction.lean)

| Candidate sum | Modulo 3 | Modulo 13 | Modulo 11 |
| ---: | --- | --- | --- |
| 372 | Fails | Passes | Passes |
| 376 | Passes | Fails | Passes |
| 380 | Passes | Passes | Fails |

Every pair of columns has a shared passing row. All three together have none. A search that asks only whether each pair can pass somewhere could keep this entire empty prefix. The next candidate, 384, also fails modulo three. The first common survivor is 388, the actual factor sum. The example pinpoints what was lost when we summarized each pair with a yes or no: the identity of its witness. [Proof for every subset of these tests](../PrimeFactors/PairwiseSumObstruction.lean)

## Why some prime must reject a wrong sum

For a wrong sum the discriminant is a positive nonsquare below $2^{2050}$. The proof assigns each positive integer a sign using the Jacobi symbol of $D$. Integers sharing a factor with $120D$ get sign zero. This choice ensures that a prime with negative sign sees a nonsquare in the original discriminant, including any square factor. A finite construction shows that a negative sign occurs. [Sign and periodicity](../PrimeFactors/DiscriminantJacobiCharacter.lean) · [Existence of a negative sign](../PrimeFactors/NonsquareJacobiWitness.lean)

Count the signs through $X=2^{1047}$. If there are $U$ nonzero signs and $B$ negative ones, their sum is $U-2B$. If every prime through $2^{940}$ had nonnegative sign, each negatively signed integer would contain a larger prime. Counting its possible cofactors gives an upper bound on $B$. A separate elementary count shows that more than one fourteenth of a full period has nonzero sign, and bounds the error for the incomplete period. Together these estimates would make the signed sum larger than the published character-sum bound permits. Thus a negative prime occurs below the cutoff. [Counting possible cofactors](../PrimeFactors/NegativeCharacterPrimeCover.lean) · [Density of nonzero signs](../PrimeFactors/FiniteUnitDensity.lean) · [Incomplete periods](../PrimeFactors/CoprimePrefixDiscrepancy.lean) · [Numerical contradiction](../PrimeFactors/UnconditionalSignBudget.lean)

The two prime-counting inputs are Rosser and Schoenfeld’s upper bound on the number of primes and their estimates for the sum of reciprocal primes. The third input is the explicit Pólya–Vinogradov inequality for a nonprincipal character, including characters induced from a smaller modulus. The Lean structure `PublishedEstimates` records their exact use. [Rosser–Schoenfeld, Corollary 1](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=6) · [Theorem 5](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf#page=7) · [Frolenkov–Soundararajan, Corollary 1](https://doi.org/10.1007/s11139-012-9462-y) · [Explicit statement in Johnston–Ramaré–Trudgian, Lemma 13](https://ramare-olivier.github.io/Maths/JRT_Submitted.pdf#page=5)
