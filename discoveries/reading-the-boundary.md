# Recovering the sum from one boundary value

Let $N=pq$ with distinct primes $p<q\le2p$. Write $L_N$ for the principal Dirichlet L-function modulo $N$. For any positive height $t$, define $B(t)=\operatorname{Re}(e^{it\log(N)/2}L_N(it)/\zeta(it))$. Expanding its two finite Euler factors gives the exact identity

$$\cos(t\log(N)/2)-B(t)/2=\cos(t\delta),\qquad \delta=(\log q-\log p)/2.$$

The entire unknown part of the function is one real frequency. This result and the decoding theorems below use classical facts about the Euler factors, independently of RH. The boundary question originated in the Riemann repository's strict-half-plane lemma. [Lean identity and decoders](../PrimeFactors/AnalyticAccess.lean) · [Original motivation](character-conjectures.md#comparing-a-factor-with-a-threshold)

## One low-height reading

The sum is $S=2\sqrt N\cosh\delta$. At $t=1$ the reading gives $\cos\delta$. Near equal factors, the functions $\cos$ and $\cosh$ both have zero first derivative. Their deviations from one remain comparable. Lean proves $|\cosh a-\cosh b|\le4|\cos a-\cos b|$ on $[0,\log 2]$. From an approximation to $B(1)$, compute the implied cosine, clip it to $[\cos(\log 2),1]$, apply arccos, then compute $2\sqrt N\cosh$ of the result and round to the nearest integer.

An absolute error strictly below $1/(8\sqrt N)$ in the normalized reading gives the **exact integer sum**. For a 2048-bit input, an error at most $2^{-1027}$ suffices. This halves the previous sufficient bit count and needs one L-value. Using a little extra precision for the elementary functions leaves room for numerical rounding. The operation count excludes obtaining the L-value. An efficient, certified evaluator from $N$ alone is open. [Lean one-reading theorem](../PrimeFactors/AnalyticAccess.lean)

## Constant accuracy at increasing heights

An adaptive alternative keeps an interval $[a,a+w]$ containing $\delta$. Choose a positive $t$ so $t(a+w/2)$ is $\pi/2$ modulo $2\pi$ and $\pi/5<tw\le\pi$. Even with error $1/10$ in the cosine reading, its sign picks one of two overlapping intervals of width $3w/4$ that contains the true value. After $O(\log N)$ readings the factor $q=\sqrt N e^\delta$ is uniquely determined. The largest needed height is $O(\sqrt N)$. Lean checks the choice of height, contraction, accumulated enclosure, and stability under perturbing the requested height. Cost per high-ordinate L-value remains unknown. [Adaptive proofs](../PrimeFactors/AnalyticAccess.lean)

There is also a fixed integer-height experiment. Take all $2^i$ and $2^i+2^j$ with $0\le i,j\le K$. For any $0\le u<v\le\pi/6$ separated by at least $\pi/(3\cdot2^K)$, Lean proves two cosine readings differ by at least $1/4$ at some height in that list. Hence readings within $1/10$ confine all compatible frequencies to an interval shorter than $\pi/(3\cdot2^K)$. Balanced log-ratios lie in this range. There are at most $(K+1)+(K+1)^2$ heights, each at most $2^{K+1}$. At each scale a dyadic height makes half the gap visible. Adding another dyadic height moves the midpoint phase away from a sine zero when reflection would hide that gap. [Finite separation and noisy resolution](../PrimeFactors/MixedHeights.lean)

**Why add heights?** The two continuous parameters $\pi/16-1/1024$ and $\pi/16+1/1024$ yield cosine values within $1/64$ at *every* pure dyadic height. From height 16 onwards the values coincide exactly. An observer allowing errors of $1/128$ can receive identical readings forever. This counterexample concerns the real frequency measurement model. Additional arithmetic conditions on a particular integer product may still distinguish candidate factors. [Lean reflection example](../PrimeFactors/MixedHeights.lean)

## What a Fourier expansion would have to recover

The finite Fourier transform of the principal character is a Ramanujan sum. For $N=pq$ its value at a frequency coprime to $N$ is 1. A frequency sharing exactly one of the primes with $N$ reveals that factor by a gcd. The constant coefficient in the unnormalized transform is $\varphi(N)$. An explicit weighted sum taken only over unit frequencies and zero therefore reduces to the sum of its unit-frequency weights plus its zero-frequency weight times $\varphi(N)$. Lean proves this for mathlib's discrete Fourier transform. [Exact transform](../PrimeFactors/FourierAccess.lean) · [Ramanujan sums and finite Fourier transforms](https://systems.caltech.edu/dsp/PPVSquare.pdf)

Suppose a finite Fourier series approximates the entire coprimality indicator on $\mathbb Z/N$ with uniform absolute error below $1/4$. Lean proves its list of frequencies contains a proper gcd witness. In the absence of frequencies divisible by $q$ but not $p$, summing the series over each fiber modulo $p$ gives the same answer. The target fiber totals at residues zero and one differ by $q-1$. Two fiber errors of at most $q\varepsilon$ would require $\varepsilon\ge(q-1)/(2q)$. This obstruction concerns uniform approximation of the full indicator. A specialized evaluator of a single boundary value can use cancellations that this argument does not address. [Fourier approximation obstruction](../PrimeFactors/FourierAccess.lean)
