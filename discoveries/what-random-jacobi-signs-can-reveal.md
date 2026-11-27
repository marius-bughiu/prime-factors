# What do random Jacobi signs reveal about the prime factors?

**For 77, the signs are visibly different from fair coin flips. For a product of two 1,024-bit primes, even a trillion sign observations are extraordinarily close to fair coin flips.** This comparison retains only the sign returned by each independent uniform draw. It concerns estimating the factor sum by sampling a histogram. A calculation that also uses the sampled residues, chooses them adaptively, or combines each sign with a weight such as $t^k$ is a different experiment. [Lean sampling proof](../PrimeFactors/JacobiHistogramSamples.lean) · [Weighted moments](when-jacobi-moments-first-change.md)

At $N=pq$, sample a uniform residue $t$ and record the Jacobi symbol of $t^2-4$ modulo $N$. Among all $N$ residues, exactly $Z=2(p+q)-4$ give zero, and the number of positive signs exceeds the number of negative signs by exactly one. The zero count therefore determines the sum of the primes. For $77=7\times11$, there are 32 zeros, 23 positive signs and 22 negative signs. [Counts over the whole product](../PrimeFactors/ProjectiveWordMoments.lean) · [Checked histogram for 77](../PrimeFactors/JacobiHistogramSamples.lean)

## The cost of replacing a whole count with a random sample

Compare $T$ independent signs with $T$ independent fair coin flips, encoded as $+1$ and $-1$. The total variation distance is the largest difference in probability the two sources can assign to **any** event on the observed sign sequence. Here it equals

$$
1-(1-Z/N)^T.
$$

A sequence containing zero occurs only under the actual sampling rule. Every individual sequence containing just plus and minus signs is at least as likely under the fair coin, since each sign has probability at most one half under the actual rule. The probability of seeing at least one zero therefore accounts for the whole distance. For two draws at 77, the mass the two distributions share is exactly $2025/5929=(45/77)^2$. [Finite product and exact overlap](../PrimeFactors/JacobiHistogramSamples.lean)

When $p,q\ge2^{1023}$, the chance of zero on one draw is less than $2^{-1021}$. For $T\le2^{40}$, the total variation distance is less than $2^{-981}$. Thus every success criterion using the product and the sampled signs has almost exactly the same probability if those signs are replaced with fair coins. This bounds the information gained from that sampling rule, independently of how much the product alone might reveal. [Full-size bound](../PrimeFactors/JacobiHistogramSamples.lean)
