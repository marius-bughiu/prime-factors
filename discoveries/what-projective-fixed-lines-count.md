# What counting fixed lines can reveal

Two matrices give the same Jacobi symbol modulo 77. One preserves four directions and the other preserves none. An exact count would distinguish them. Lean verifies that, for an invertible matrix whose discriminant is coprime to an odd semiprime, obtaining that count is equivalent to deciding whether the discriminant has a square root modulo the product. [Fixed-line classification and checked example](../PrimeFactors/ProjectiveFixedLines.lean)

## Four directions or none on 77

A fixed line is a direction that a matrix preserves, even if it scales vectors along that direction. Over a prime field the directions are the slopes $z$ represented by $(z,1)$ and one more represented by $(1,0)$. Over $77=7\times11$, a direction consists of one choice at each prime. This includes directions with a finite slope at one prime and the extra direction at the other. The two local fixed-line counts multiply. [Lean proof of the product count](../PrimeFactors/ProjectiveFixedLines.lean)

For the two matrices below both determinants are 1, and every fixed line has a finite slope. The fixed-line equation is particularly simple because the diagonal entries agree. For a matrix with upper-right entry $b$ and lower-left entry $c$, it reduces to $cz^2=b$ in this example.

| Matrix, shown by rows | Fixed-line equation mod 77 | Discriminant mod 77 | Jacobi symbol | Fixed slopes mod 77 |
| --- | --- | ---: | ---: | --- |
| $(24,23),\ (25,24)$ | $z^2=4$ | 67 | $+1$ | 2, 9, 68, 75 |
| $(14,13),\ (15,14)$ | $z^2=6$ | 10 | $+1$ | None |

The first discriminant is a square at both primes. The second is a nonsquare at both. Multiplying the two local signs gives $+1$ either way. Testing all 77 slopes verifies the table directly. The formal example `jacobi_counterexample` checks the Jacobi symbols and the two counts. [Lean example](../PrimeFactors/ProjectiveFixedLines.lean)

## What a count would supply

Let $N=pq$ for distinct odd primes and let $\Delta=(a-d)^2+4bc$ for an invertible matrix with rows $(a,b),(c,d)$. If $\gcd(\Delta,N)=1$, the total count is four exactly when $\Delta$ is a square modulo $N$, and zero otherwise. A negative Jacobi symbol already settles the zero case. Conversely, given any unit $x$ modulo $N$, the matrix with rows $(0,x),(1,0)$ has a fixed line for each solution of $z^2=x$ and no others. Thus a procedure that cheaply counted fixed lines on all such inputs would also cheaply decide quadratic residuosity. Computing that decision from the product and constructing an actual square root are separate computational questions. [Lean equivalence in both directions](../PrimeFactors/ProjectiveFixedLines.lean) · [Classical finite-field fixed-point counts, p. 4](https://arxiv.org/pdf/0910.3193#page=4)

When the discriminant vanishes at just one prime, its gcd with the product gives that prime. At a prime where it vanishes, a nonscalar matrix has one fixed line and a scalar matrix has all the lines. These cases complete the local classification. [Local counts in Lean](../PrimeFactors/ProjectiveFixedLines.lean)

## What raising one matrix to a power changes

Every power of a two-by-two matrix $A$ has the form $uA+vI$. At each prime, a nonscalar power preserves exactly the original fixed lines. A scalar power preserves every direction. To check for a scalar matrix, compare its two diagonal entries and test both off-diagonal entries for zero. If these three conditions hold at just one of the primes, taking their common gcd with $N$ already yields a proper divisor. [Lean proof for every power](../PrimeFactors/ProjectiveWordCounts.lean) · [Scalar test and gcd proof](../PrimeFactors/ProjectiveFixedLines.lean)

For example, cubing the first matrix in the table gives rows $(15,70),(56,15)$ modulo 77. The cube is scalar at 7 and nonscalar at 11. Its fixed-line count rises from four to $8\times2=16$. The entries give $\gcd(77,70,56)=7$ before counting any lines. If a power is scalar at both primes, its count is $(p+1)(q+1)$, from which subtracting $N+1$ gives $p+q$. Recognizing that a matrix is scalar is easy. Evaluating that total on an unknown product is the missing step. The power theorem covers repetitions of one generator. Products of distinct matrices require a separate analysis. [Proof of the scalar total](../PrimeFactors/ProjectiveFixedLines.lean) · [Scope of the power theorem](../PrimeFactors/ProjectiveWordCounts.lean)
