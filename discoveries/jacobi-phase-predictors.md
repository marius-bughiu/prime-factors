# What affine Jacobi tests reveal about the hidden phase

Let $N=pq$ for distinct odd primes. The target is $B_h(t)=\operatorname{sign}\cos(2\pi ht/N)$, where $h^2=1\pmod N$ and $h\ne\pm1\pmod N$. An advantage over chance on uniform frequencies, together with the ability to query the predictor at chosen inputs, would suffice for randomized factor recovery. One inexpensive candidate is to compute $k$ Jacobi symbols
$$
 X_i(t)=\left(\frac{a_it+b_i}{N}\right)\in\{-1,0,1\}
$$
and combine their values. We allow any coefficients depending on $N$, repeated shifts, and any ternary decision table $F$, even one chosen with knowledge of the target. The coefficients and table are fixed before seeing $t$. During prediction its only information about $t$ is the feature word. Independent randomized choices of such predictors satisfy the same bound by averaging. Computing a Jacobi symbol uses the Euclidean algorithm and needs only the public modulus. [Weak-sign reduction](predicting-random-salie-signs.md)

Write $H_m=\sum_{j=1}^m1/j$. The absolute difference between this predictor's success probability and $1/2$ is at most
$$
 k\left(\frac1p+\frac1q\right)
 +\frac12\left(\frac1p+\frac1q+\frac1N\right)
 + H_{(N-1)/2}\,\frac{2^{k/2}k^2}{\sqrt N}.
$$
For 1,024-bit primes, this gives the following bounds. The same rounded bounds hold when the evaluation frequency is conditioned to be a unit.

| Fixed affine tests | Maximum advantage over chance |
| ---: | ---: |
| 512 | $2^{-738}$ |
| 1,024 | $2^{-480}$ |
| 1,536 | $2^{-223}$ |
| 1,900 | $2^{-40}$ |

Here $p,q\ge2^{1023}$ and $H_{(N-1)/2}\le1+\log N<1421$. Conditioning changes any success probability by at most $1/p+1/q$. The common upper numerator with denominator $2^{1023}$ is $1421k^2 2^{k/2}+2k+4$. [Lean finite estimates](../PrimeFactors/PhaseCharacters.lean)

## Uniform frequencies and zero symbols

A form that vanishes identically modulo either prime always returns zero and can be removed. Each remaining form has at most one root at each prime, including the case of a nonzero constant form at that prime. Thus any remaining feature is zero on a set of density at most $1/p+1/q$. If a public slope has a proper gcd with $N$, that gcd already supplies a factor independently of any prediction.

Restrict $F$ to the Boolean cube and expand it in products of coordinate signs, writing $c_S$ for its Walsh coefficients. Parseval on the uniform Boolean cube gives $\sum_S|c_S|^2\le1$, so $\sum_S|c_S|\le2^{k/2}$. Actual feature signs may be dependent. Evaluating this multilinear expansion when some coordinates are zero averages the Boolean table over independent uniform completions of those coordinates. The resulting function $G(t)$ has magnitude at most one and equals the given table whenever all signs are nonzero. Replacing the table by $G$ changes correlation with $B_h$ by at most $2k(1/p+1/q)$. [Lean Walsh transfer inequality](../PrimeFactors/PhaseCharacters.lean)

For an additive frequency $u$ coprime to $N$, the normalized Fourier transform of each monomial $\prod_{i\in S}X_i(t)$ splits by CRT into normalized sums over $p$ and $q$. The local additive phases are nontrivial at both primes. At a prime $r$, remove nonzero constants and write the local polynomial as a scalar times linear factors grouped by their distinct roots. Keep the roots of odd multiplicity in a squarefree polynomial, with $d_o$ roots. A root of positive even multiplicity deletes a summand from this reduced character sum. Write $d_e$ for their number. For $d_o>0$, Katz's Theorem 1.1 with one variable, a nonzero linear additive phase and the quadratic character gives a bound $d_o\sqrt r$ before those deletions. When $d_o=0$, the complete additive sum of a constant is exactly zero. The total bound is consequently $d_o\sqrt r+d_e\le |S|\sqrt r$ in both cases. This covers shifts that coincide at just one prime. The empty monomial has zero transform at $u$. Multiplying the local bounds and summing with weights $c_S$ gives $|\widehat G(u)|\le 2^{k/2}k^2/\sqrt N$. [Katz, *Estimates for Mixed Character Sums*, Theorem 1.1](https://web.math.princeton.edu/~nmk/charsum15.pdf)

To account for the remaining additive frequencies, average $B_h$ on a fixed class modulo $p$. Multiplication by $h$ permutes this class onto another class modulo $p$. The positive target interval has $(N\pm1)/2$ consecutive residues on the circle. It contains either $(q-1)/2$ or $(q+1)/2$ of the $q$ residues in that class. The conditional mean therefore has absolute value $1/q$. The corresponding mean modulo $q$ has magnitude $1/p$, and the full mean has magnitude $1/N$. The sum of the two conditional means minus the full mean is exactly the Fourier projection onto the nonunit frequencies, including zero. Indeed, class averaging keeps precisely the additive characters constant on each class, and the two retained sets intersect only at frequency zero. Its correlation with $G$ is bounded by $1/p+1/q+1/N$. On the unit frequencies use the bound on $\widehat G$ above and the absolute Fourier mass of $B_h$, at most $2H_{(N-1)/2}$ away from zero. Dividing correlation by two gives the stated advantage. [Interval coefficient bound](predicting-random-salie-signs.md)

## How many shifts could identify the input?

For balanced primes $3\le p<q\le2p$, about $\log_2 N$ ternary tests can carry enough information to label almost every input, if the decision table has unrestricted size. Take features $X_s(t)=((t+s)/N)$ at independent uniform shifts $s$. For fixed $t\ne u$, the probability that a single test gives the same answer on both is at most $1/2$.

For the calculation, let $X=X_s(t)$ and $Y=X_s(u)$. Then $2\Pr(X=Y)=\Pr(XY\ne0)+\mathbb E(XY)+2\Pr(X=Y=0)$. At a prime $r$ the unnormalized sum of the product of two shifted quadratic characters is $-1$ for distinct shifts and $r-1$ for equal shifts. In the distinct case, $1+(t-u)/(s+u)$ runs through the field when inversion at zero is defined to return zero. Away from $s=-u$ its quadratic character equals that of $(s+t)(s+u)$ by removing a nonzero square. At the exceptional point the former is one and the latter zero. The complete nontrivial character sum is zero, giving $-1$. CRT multiplies the local expectations. Counting zeros in the same two fields gives the exact probabilities below. [Lean autocorrelation and ternary identity](../PrimeFactors/PhaseCharacters.lean)

| Relation between $t$ and $u$ | Numerator of $2N\Pr(X=Y)$ |
| --- | ---: |
| Different modulo both $p,q$ | $N-2p-2q+9$ |
| Equal modulo $p$ only | $N+q-3p+3$ |
| Equal modulo $q$ only | $N+p-3q+3$ |

Each numerator is at most $N$ under the balance assumption. Thus after $k$ independent shifts each fixed pair collides with probability at most $2^{-k}$. By the union bound, the expected fraction of inputs sharing a word with another input is at most $(N-1)2^{-k}$. Some fixed shift family therefore identifies all but a $2^{-s}$ fraction at $k=\lceil\log_2 N\rceil+s$. Assigning each unique word its target label would require access to those labels and can use a table of order $N$. This establishes the information capacity of the features. An efficient rule that computes the labels from the product remains a separate requirement.
