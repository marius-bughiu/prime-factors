# How many factor sums pass a test at one large prime?

**Between 43.75% and 56.25% pass** on the first $2^{521}$ candidate sums in the stride-12 search for the repository’s 2048-bit example called `separatedN`. The test asks whether $S^2-4N$ is a square modulo one 1024-bit prime. The true sum $S=p+q$ always passes, because its discriminant equals $(p-q)^2$. Many false sums pass too. Here the number of survivors is at least $7\cdot2^{517}$, and at most one can be the sum of the two prime factors. [Checked counting theorem and example](../PrimeFactors/ShortDiscriminantWindow.lean)

The window and the test can both be set up from public values. Its first sum is the smallest $S\ge2\sqrt N$ with $S\equiv N+1\bmod12$. Each subsequent sum increases by 12. Lean checks that even the last position fits the upper bounds for two odd 1024-bit factors. The test prime is `adjacentSmall`, a certified prime from a different example, coprime to this input. The count holds for this specific starting sum, even though the window covers only a fraction of the test prime’s period. [Public inputs](../PrimeFactors/GroupedNormExamples.lean)

For the general bound, take any odd prime $\ell$ and any progression $a+bj$ of length $\sqrt\ell<L\le\ell$, with $\ell$ dividing neither $b$ nor $N$. Let $A$ count positions $0\le j<L$ for which $(a+bj)^2-4N$ is a square modulo $\ell$, including zero. Then

$$
 |2A-L|\le(2\sqrt\ell+2)\log\!\left(\frac{4e^8L}{\sqrt\ell}\right).
$$

The proof counts residues $x$ with $x+N/x=S\bmod\ell$. They normally come in pairs. The at most two exceptions satisfy $x^2=N\bmod\ell$ and account for the additive 2 in the bound. Weil’s complete Kloosterman-sum estimate controls the Fourier coefficients of the test. The short-sum estimate of Fouvry, Kowalski, Michel, Raju, Rivat and Soundararajan controls the error over the specified window. Lean takes these two published results as explicit hypotheses and verifies the deduction and finite constants. [Weil’s original paper](https://doi.org/10.1073/pnas.34.5.204) · [Short-sum theorem 1.1, equation (1.5)](https://arxiv.org/html/1508.00512#S1.Thm1)

The count bound requires no scan. Applying the test separately to every position in the example would require $2^{521}$ modular square tests. Recovering the factors would still require locating a sum with an integer-square discriminant. The bound gives neither that location nor a guarantee that it lies in this prefix.
