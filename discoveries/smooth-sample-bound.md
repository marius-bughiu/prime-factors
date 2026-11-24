# How often can a random square give a smooth remainder?

Suppose only $N$ is supplied, $2^{2047}\le N<2^{2048}$, and $N=pq$ for distinct 1,024-bit primes. Choose a unit $x$ uniformly modulo $N$ and take the representative of $x^2\bmod N$ closest to zero. Even after $2^{48}$ samples, the probability of seeing a single remainder with all prime factors at most $2^{32}$ is at most **$2^{-377}$**. The bound holds for every such product. Drawing the primes at random preserves it. A smooth remainder provides a row in a relation search. A factor requires further arithmetic. [Dixon's random squares algorithm](https://doi.org/10.1090/S0025-5718-1981-0595059-1)

| Largest allowed prime $B$ | One sample | At least one in $2^{48}$ samples | One sample that is also at most $2^{1024}$ in absolute value |
|---|---:|---:|---:|
| $2^{16}$ | $\le 2^{-1014}$ | $\le 2^{-966}$ | $\le 2^{-1448}$ |
| $2^{24}$ | $\le 2^{-614}$ | $\le 2^{-566}$ | $\le 2^{-1272}$ |
| $2^{32}$ | $\le 2^{-425}$ | $\le 2^{-377}$ | $\le 2^{-1191}$ |

## From a smooth integer to a sample probability

Write $A=(N-1)/2$, $\varphi(N)=(p-1)(q-1)$, and $\Psi(W,B)$ for the number of positive integers up to $W$ with all prime factors at most $B$, including 1. Every nonzero unit square has four roots by the Chinese remainder theorem. Its two local roots at each prime are opposites. For $W\le A$ the exact probability is

$$
\frac4{\varphi(N)}
\sum_{\substack{1\le s\le W\\s\ B\text{-smooth}}}
\big(\mathbf 1_{s\text{ is a unit square mod }N}
    +\mathbf 1_{-s\text{ is a unit square mod }N}\big)
\ \le\ \frac{8\Psi(W,B)}{\varphi(N)}.
$$

Setting $W=A$ gives the full centered interval. A union bound multiplies the single-sample probability by the number of draws. Uniformity of each draw suffices. For independent draws of individual success probability $P$, the exact probability is $1-(1-P)^T$. A search that constructs small remainders directly has a different sampling law.

The hidden congruence classes can give a sharper count. If at least one hidden prime is $3\bmod4$, at most one of $s,-s$ can be a square, halving the upper bound. If **both** are $3\bmod4$ and $B<\min(p,q)$, exactly one sign works if and only if the public Jacobi symbol $(s/N)$ is $+1$. Indeed, changing the sign flips both local Legendre signs at once. For $N=77$, $W=38$ and $B=5$, there are 20 smooth positive integers and 10 have Jacobi symbol $+1$. Exactly 40 of the 60 units produce an accepted centered square.

## A finite upper bound for the smooth integer count

For $\sigma>0$, each $B$-smooth $s\le W$ contributes at least one to the weighted sum of $(W/s)^\sigma$. Extending the sum to all positive $B$-smooth integers and multiplying geometric series over the allowed primes gives Rankin's inequality

$$
\Psi(W,B)\le W^\sigma Z_B(\sigma),\qquad
Z_B(\sigma)=\prod_{\ell\le B,\ \ell\text{ prime}}(1-\ell^{-\sigma})^{-1}.
$$

The certified integer exponents below can also be used to bound searches with separate smooth numerators and denominators. They count every eligible positive integer without a quadratic-residue restriction. [Hildebrand and Tenenbaum on the finite Euler product](https://tenenb.perso.math.cnrs.fr/PPP/Psi%2B.pdf) · [Lean proof of Rankin's inequality](../PrimeFactors/SmoothSampleBound.lean)

| $B$ | $\Psi(2^{1024},B)$ | $\sigma$ at $2^{1024}$ | $\Psi(2^{2047},B)$ | $\sigma$ at $2^{2047}$ |
|---|---:|---:|---:|---:|
| $2^{16}$ | $\le 2^{596}$ | $119/256$ | $\le 2^{1030}$ | $101/256$ |
| $2^{24}$ | $\le 2^{772}$ | $172/256$ | $\le 2^{1431}$ | $159/256$ |
| $2^{32}$ | $\le 2^{853}$ | $197/256$ | $\le 2^{1620}$ | $187/256$ |

For the full interval, $0<\sigma<1$ makes $(N/2)^\sigma/N$ decrease as $N$ grows. Substituting the **lower** endpoint $2^{2047}$ therefore gives a uniform upper bound for every admissible $N$. This yields

$$
P \le 8\,(1-2^{-1023})^{-2}\, 2^{2046\sigma-2047} Z_B(\sigma).
$$

Here $2^{2046}$ arises only after combining the numerator and denominator. The actual half-width can approach $2^{2047}$. For a fixed $W=2^{1024}$, replace $2046\sigma$ by $1024\sigma$ in this display. More generally a fixed interval containing $w$ residue classes has hit probability at most $4w/\varphi(N)$ regardless of smoothness. A centered, predetermined square-root-sized interval therefore costs about a thousand bits of sampling probability by itself. The smoothness frequency conditional on hitting the interval would require a separate count of its quadratic residues.

## Reproducing the integer certificates

Run `python3 experiments/smooth_sample_bound.py` for all rows, or append `--base-bits 16` for the smallest case. A segmented sieve counts primes in 256 equal subdivisions of each dyadic interval, with duplicate endpoints removed for small primes. The actual prime counts are 6,542, 1,077,871 and 203,280,221. Using each bin's lower endpoint $L$ gives an upper bound on every logarithmic Euler factor in that bin. [Certificate program](../experiments/smooth_sample_bound.py)

For $\sigma=a/d$ in lowest terms the program finds an integer $q$ satisfying $q^d L^a\ge (2^{48})^d$. Thus $z=q/2^{48}$ bounds $L^{-\sigma}$ from above. It sums the first 16 terms of $-\log(1-z)$ with upward integer rounding and adds $z^{17}/[17(1-z)]$ for the tail. To convert to bits, it divides by a lower bound on $\log 2$, the first eight terms of $2\sum_{k\ge0}3^{-(2k+1)}/(2k+1)$. The correction $-2\log_2(1-2^{-1023})$ is smaller than $1/1024$ since $-\log(1-u)\le u/(1-u)$ and $\log 2>1/2$. Floating point only selects the trial exponent and proposes a starting integer $q$. The certificate uses integer inequalities and rational arithmetic.
