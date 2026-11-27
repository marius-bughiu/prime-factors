# When does a Jacobi moment first reveal a prime?

For 77, a sum of public signs gives 42 at degree six. A formula valid at all lower degrees predicts 20. Their difference, 22, has greatest common divisor 11 with 77. Lean proves that for every product of two distinct odd primes, the first such discrepancy occurs at exactly one less than the smaller prime. Finding that degree by counting is expensive. For two 1,024-bit primes an ascending scan would have to reach a degree of at least $2^{1023}-1$. [Lean proof](../PrimeFactors/ProjectiveWordMoments.lean)

## Two counts from the same matrices

Write $N=pq$ with $p<q$. For each residue $t$ consider the determinant-one matrix

$$
 A_t=\begin{pmatrix}t&-1\\1&0\end{pmatrix}.
$$

Over either prime, the point at infinity moves. A finite point $x$ stays fixed precisely when $x^2-tx+1=0$. Such an $x$ is a unit and determines exactly one matrix parameter, $t=x+x^{-1}$. The Chinese remainder theorem pairs the local fixed points. Summing their counts over all $N$ matrices therefore gives exactly $(p-1)(q-1)$. Knowing that total would give $p+q$ by subtracting it from $N+1$. Evaluating one matrix’s fixed-line count can itself require deciding whether a residue is a square at both unknown primes. [Fixed-line classification](../PrimeFactors/ProjectiveFixedLines.lean)

There is a sign we can compute from each parameter using only integer remainders, the Jacobi symbol $J_t=(\frac{t^2-4}{N})$. Its sum across all parameters is always 1. Its zeros do encode the factors’ sum. The discriminant vanishes at the two residues $\pm2$ modulo each prime, giving exactly $2(p+q)-4$ zeros modulo $N$. Counting them by scanning the modulus takes $N$ tests. At a zero one can also check the discriminant’s gcd with $N$ directly.

## What changes at the boundary?

The degree-$k$ moment is $M_k=\sum_{t\bmod N}t^kJ_t\pmod N$. For every $k<p-1$ the result is determined in advance. For odd $k$ it is zero. For even $k$ it is the middle binomial coefficient $C_k=\binom{k}{k/2}$ reduced modulo $N$. Write $C_k=0$ at odd degrees. This also determines any polynomial-weighted sum modulo $N$ below the same degree by combining the corresponding coefficients. The theorem applies to a complete sum over residues. It supplies no formula for incomplete intervals or for the unreduced integer value of a weighted sum.

The middle coefficient appears when one expands $(x+x^{-1})^k$ over all nonzero residues modulo a prime. Nonconstant powers sum to zero in the field whenever their exponent has absolute value strictly below the order of the multiplicative group. At $k=p-1$, the two endpoint powers $x^{p-1}$ and $x^{-(p-1)}$ start to contribute. After subtracting the unweighted field power sum, the discrepancy is exactly one modulo $p$. The larger prime still satisfies the original degree bound at $k=p-1$, so the discrepancy is zero modulo $q$. Consequently $\gcd(M_{p-1}-C_{p-1},N)=q$.

Ordinary binary search on the equality test has no monotonicity guarantee, even if it skips all odd degrees. At level 15 the measured and predicted values disagree at degree 2 (12 versus 2) and agree again at degree 10 (both 12). At level 77 both values return to zero at degree 60.

## Cost on small products

The checker constructs primitive projective coordinates directly from each product and checks every matrix against every point. Separately, it computes the $N$ Jacobi signs once and uses them at successive degrees until the first mismatch. It consults the fixture’s expected factors only after these measurements. Lean also checks the five prime factorizations. All moment entries below are residues modulo the input. [Reproducible checker](../experiments/projective_word_moments.py)

| Product | Point tests | Fixed-line total | First exceptional degree | Predicted | Measured | Weighted terms summed across degrees |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 15 | 360 | 8 | 2 | 2 | 12 | 45 |
| 35 | 1,680 | 24 | 4 | 6 | 27 | 175 |
| 77 | 7,392 | 60 | 6 | 20 | 42 | 539 |
| 143 | 24,024 | 120 | 10 | 109 | 44 | 1,573 |
| 221 | 55,692 | 192 | 12 | 40 | 210 | 2,873 |

Run `python3 -m experiments.projective_word_moments` to reproduce the table. The direct scan sums $pN$ weighted terms from degree zero through degree $p-1$, in addition to preparing the signs. Testing the integers $2,3,\ldots,p$ as possible divisors finds the same first prime in $p-1$ divisions. Supplying that final degree would already identify the smaller prime. The low-degree formula is inexpensive for small degrees and gives the same prescribed residue on every eligible input. A way to select and evaluate an informative high degree cheaply from the product remains open.
