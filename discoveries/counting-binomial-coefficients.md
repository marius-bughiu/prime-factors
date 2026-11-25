# How much can a different window size save?

On the two public 2,048-bit products, even a scheduler that changes polynomial degree, Taylor depth, center and radius at every step must account for more than $2^{508}$ coefficient slots on the fresh input and more than $2^{509}$ on the crossed input to cover the full odd smaller-factor range using the ordinary binomial determinant tests. The existing 24,576-row schedule is within a factor of **3.83** and **3.63**, respectively, of every such complete alternative, using the sharper counts below. A slot is one entry in a dense coefficient vector of length $k+1$. The charge measures the size of the vectors listed for the sweep. Caching or generating coefficients implicitly can change the machine work. [Verified work bounds](../PrimeFactors/BinomialWindowWork.lean) · [Published complete schedule](integer-valued-factor-windows.md)

The domain consists of every odd integer $d$ from $\lceil N/(2^{1024}-1)\rceil$ through $\lfloor\sqrt N\rfloor$. Every smaller 1,024-bit prime factor of these products lies in this domain. The comparison charges one dense vector for each invocation, even when windows overlap. It applies to complete geometric coverage and permits different public divisor floors $D$ up to $\sqrt N$ in different windows. Skipping positions by a separate number-theoretic argument, using a sparse representation, using an observed short row beyond the sufficient determinant test, or stopping at the first factor changes the work being measured.

## A necessary bound at any degree

Let $k$ be the degree, $m$ the depth, $B=k(k+1)/2$, and $T=m(m+1)/2$. In a one-sided window of index span $H$, put $V=\prod_{i=0}^k\binom Hi$. For a centered window of index radius $H$, the positive half alone requires these same column bounds. Both the finite box criterion and the numerical LLL criterion imply the weaker inequality $N^T V<D^{m(k+1)}$. Since $D^2\le N$, raising to the fourth power and using $(k-2m)^2\ge0$ gives $V^4<N^B$. In particular, $V<J^B$ for any positive integer $J$ with $N\le J^4$. [Volume and centered-weight inequalities](../PrimeFactors/BinomialWindowWork.lean)

We also have $\binom Hi i!\ge\max(0,H+1-k)^i$ for $0\le i\le k$, using the smallest available factor in the falling factorial. To combine the columns, keep every factor of every $i!$. Their triangular list has $B$ entries and sum $B(k+2)/3$. The arithmetic–geometric mean inequality therefore gives

$$3^B\prod_{i=0}^k i!\le(k+2)^B.$$

Together these comparisons give $3\max(0,H+1-k)<(k+2)J$. For $k\ge3$ this bounds the $2H+1$ positions of a centered window by $5(k+1)(J+3)/6$. The proof handles degrees one and two directly from the volume inequality. A one-sided window covers fewer positions under the same estimate. [Factorial bound and cost per window](../PrimeFactors/BinomialWindowWork.lean)

## From one window to the full range

If $P$ is the number of odd candidates and $C$ the sum of all $k+1$ charges, summing the individual bounds yields $6P\le5(J+3)C$. This works for any finite family that covers the domain, including a family produced by following adaptive choices to completion. The proof uses the following public rounded bounds on the roots of $N$. The numerical powers of two in the last column round the proved lower bounds downward.

| Input | Upper bound $J$ on the fourth root | Bracket for the square root | Coefficient-slot lower bound |
|---|---:|---|---:|
| Fresh | $3844\cdot2^{500}$ | $[57719,57720]\cdot2^{1008}$ | $>2^{508.10}$ |
| Crossed | $3551\cdot2^{500}$ | $[49228,49229]\cdot2^{1008}$ | $>2^{509.04}$ |

For comparison with the scheduled work, the proof uses the lower square-root endpoint to count candidate positions and the upper endpoint to bound the published number of windows. The integer comparisons use only $N$ and the endpoint formulas. Lean checks the whole-bit lower bounds and the factors 3.83 and 3.63 directly. [Control receipts](../PrimeFactors/BinomialWindowWork.lean)

The project’s rounded Chebyshev polynomials in binomial coordinates have a different sufficient test. On the window $0\le x\le4U$, their degree-$i$ column weight is at least $\binom Ui$. The same calculation therefore gives more than $2^{507}$ slots on the fresh product and $2^{508}$ on the crossed product even when ordinary and rounded windows are mixed. Within this broader class the original schedule costs less than 7.66 or 7.26 times the respective alternatives. This extension uses the published rounding weights. A sharper column estimate would need its own analysis. [Rounded columns](../PrimeFactors/RoundedChebyshevWindows.lean) · [Mixed-cover bound](../PrimeFactors/BinomialWindowWork.lean)
