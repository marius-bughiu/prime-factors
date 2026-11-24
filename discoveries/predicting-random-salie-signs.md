# Factoring from a weak sign prediction

Fix an odd product $N=pq$ of distinct primes. Let $h$ be a mixed square root of one modulo $N$, with opposite signs modulo the two primes. The two choices $h,-h$ give the same target
$$
 B_h(t)=\operatorname{sign}\cos(2\pi th/N).
$$
For a supplied lower bound $0<\varepsilon\le1/2$, suppose a procedure, given $N$ and a chosen $t$, predicts this bit with probability at least $1/2+\varepsilon$ averaged over uniform $t\in\mathbb Z/N$ and any internal randomness. Then a randomized algorithm recovers a factor in time polynomial in $\log N$ and $1/\varepsilon$, plus the cost of its predictor calls. The advantage can depend on this particular product. An inverse-polynomial advantage in the bit length suffices. The quarter boundaries never occur since $N$ is odd.

For a unit $t$, the target is the sign of the normalized Salié sum $F(t)$ minus the public threshold $2\cos(2\pi t/N)$. The same reduction works for a predictor whose promise is only over uniform units. Return the known sign at zero. A queried nonzero nonunit gives a proper gcd immediately. In the proof, one can imagine completing the oracle correctly on those residues using that split. The cost of finding an efficient predictor with this advantage on independent large primes remains open. [Salié evaluation and normalization](divisor-samples.md)

The full reduction below is a paper argument. Lean checks the sign count, coefficient estimates, tail bound, an abstract correlation lemma and the arithmetic that extracts a factor. The point-query algorithm comes from Akavia, Goldwasser and Safra. [Lean proofs](../PrimeFactors/WeakPhase.lean) · [Theorem 6](https://www.cs.tau.ac.il/~safra/PapersAndTalks/hardcore.pdf)

A predictor that reads at most 512 bits of the frequency, taking each next bit from either end, gains at most $2^{-510}$ in success probability for two 1,024-bit primes. This bound allows unrestricted knowledge of the product. [Proof for this class of predictors](short-phase-predictors.md)

## Why correlation survives at a small harmonic

Write $B=B_1$ and use $\widehat f(j)=N^{-1}\sum_t f(t)e^{-2\pi ijt/N}$. The positive residues of $B$ form one cyclic interval of length $2\lfloor N/4\rfloor+1$. Its signed sum is $+1$ for $N\equiv1\pmod4$ and $-1$ for $N\equiv3\pmod4$. Thus $|\widehat B(0)|=1/N$. For $j\ne0$, let $d=\min(j,N-j)$ using the least nonnegative representative. The Fourier coefficient is twice the normalized exponential sum of that interval. The finite geometric series has magnitude at most $1/|\sin(\pi j/N)|$ before normalization. The bound $\sin(\pi d/N)\ge2d/N$ gives $|\widehat B(j)|\le1/d$. This is the interval case of the concentration estimate for multiplication codes in Akavia, Goldwasser and Safra. [FOCS 2003, §5.3, Claim 4.1](https://people.csail.mit.edu/akavia/2003-focsAGS.pdf) · [Lean coefficient and sign-count bounds](../PrimeFactors/WeakPhase.lean)

Put $K=\lceil32/\varepsilon^2\rceil$. If $N\le2K+1$, ordinary trial division takes $O(1/\varepsilon)$ divisions. Otherwise $K<N/2$. The squared Fourier mass for $d>K$ is at most $2/K$, by telescoping $1/d^2\le1/(d-1)-1/d$. The absolute coefficient sum for $1\le d\le K$ is at most $2H_K$, where $H_K=\sum_{j=1}^K1/j$.

Consider a fixed Boolean oracle $g$ with correlation $\mathbb E_t[g(t)B_h(t)]\ge\varepsilon$. Parseval gives
$$
 \mathbb E_t[g(t) B_h(t)]
   =\sum_j \widehat g(jh)\overline{\widehat B(j)} .
$$
The zero-frequency contribution has magnitude at most $1/N\le\varepsilon/4$. The contribution for $d>K$ has magnitude at most $\sqrt{2/K}\le\varepsilon/4$, by Cauchy–Schwarz and $\sum_k|\widehat g(k)|^2=1$. Multiplication by $h$ permutes all frequencies. At least $\varepsilon/2$ remains on the nonzero low harmonics, so one $j$ with $1\le|j|\le K$ satisfies $|\widehat g(jh)|\ge\varepsilon/(4H_K)$. The learner does not need to know this $j$. [Lean tail and correlation truncation](../PrimeFactors/WeakPhase.lean)

## Learning the frequency and checking a divisor

Use Theorem 6 of Akavia, Goldwasser and Safra with squared-magnitude threshold $\tau=(\varepsilon/(8L))^2$, where $L=1+\lceil\log_2 K\rceil\ge H_K$. Given point-query access to a fixed Boolean function on the additive cyclic group, the theorem returns a list of $O(1/\tau)$ frequencies containing all coefficients above threshold with probability at least $1-\delta$. The reported running time is $\widetilde O(\log N\,\log^2(1/\delta)/\tau^{5.5})$. The group generator $1$ and its additive order $N$ are public. The theorem requires the ability to query selected inputs, even though the predictor's accuracy is measured on uniformly random inputs. A stored list of unrelated random labels does not supply that interface. [FOCS 2003, §7.2, Theorem 6](https://people.csail.mit.edu/akavia/2003-focsAGS.pdf)

For each listed frequency $k$ and $1\le j\le K$, check $\gcd(j,N)$ and $\gcd(k+j,N)$, accepting a proper divisor after exact division. For the guaranteed match $k\equiv\pm jh$, a nonunit $j<N$ already splits $N$. Otherwise $k+j$ is zero at one prime and equals $2j$ modulo the other. This uses $O(K/\tau)$ gcd checks on $O(\log N)$-bit integers. At one percentage point of advantage, the conservative parameters are $K=320{,}000$ and $1/\tau=256{,}000{,}000$. Their product is 81.92 trillion. The Fourier search's bound is a theoretical oracle running time. The theorem allows extra frequencies in its output, all handled by the same integer checks. [Lean gcd proof](../PrimeFactors/WeakPhase.lean)

A deterministic predictor with agreement $1/2+\varepsilon$ already has correlation at least $2\varepsilon$. For a randomized predictor with fresh independent coins, cache its first response at each queried residue during one learner run. This implements a fixed random Boolean table without ever allocating $N$ entries. Its uniform correlation $C$ has mean at least $2\varepsilon$ and variance at most $1/N$, since its entries are independent signs. Thus $\Pr(C<\varepsilon)\le1/(N\varepsilon^2)<1/64$ on the large-$N$ branch. With $\delta=1/8$ the success probability exceeds $3/4$. Independent repetitions with fresh caches amplify it, and every accepted divisor is checked exactly.

For a finite example, take $N=77$ and mixed root $34$. The Boolean table $g(t)=-B(25t)$ agrees on 52 of 77 residues. The supplied frequency $25\equiv3\cdot34\pmod{77}$ gives $\gcd(25+3,77)=7$. This fixture illustrates a third-harmonic match. The table uses an input-specific frequency. [Kernel-checked example](../PrimeFactors/WeakPhase.lean)
