# Three Salié evaluations for an arithmetic progression

For a product $N=pq$ of distinct odd primes, three Salié evaluations suffice to approximate the hidden cosine at every frequency in a prescribed arithmetic progression of length $R$. The starting frequency and the step can be as large as $N$. To retain $b$ output bits uniformly, the three input readings need $b+2\log_2 R+O(1)$ bits. On a bounded example, 24 hidden cosines cost three direct sums with 5,040 unit terms in total. A second result explains why constructing the coefficient table for arbitrary frequencies presents a different problem. Deciding whether one regular coefficient vanishes can decide quadratic residuosity modulo $N$. [Finite Lean proofs](../PrimeFactors/PhaseEvaluation.lean) · [Definition and normalization of the Salié sum](divisor-samples.md)

## Reusing a progression step

Let $h$ be either mixed square root of one modulo $N$ and write $c_t=\cos(2\pi t h/N)$. The normalized Salié sum at a unit frequency gives $c_t$ after subtracting its public cosine and dividing by two. The concealed cosine itself is well defined for every $t$. A zero frequency gives $c_0=1$, and a proper nonunit gcd splits $N$ directly. For a progression $t_j=T+jD$, use three full readings for $c_D,c_T,c_{T+D}$, omitting repeated or public values. Cosine addition gives the exact second-order recurrence

$$
 f_j=c_{T+jD},\qquad f_{j+2}=2c_D f_{j+1}-f_j.
$$

Clamp the measured $c_D$ to $[-1,1]$ and call it $x$. Let the error of each of the three starting values be at most $\varepsilon$, including their conversion to fixed-point. Starting from the two measured outputs, set $g_{i+2}$ to the rounded value of $2xg_{i+1}-g_i$, with absolute rounding error at most $\rho$ per step. For all $j\ge1$,

$$
 |g_j-f_j|\le (2j-1)\varepsilon+
 \tfrac12j(j-1)(2\varepsilon+\rho).
$$

To see why no exponential error factor is needed, write $e_i=g_i-f_i$. Its recurrence has additive defect bounded by $\tau=2\varepsilon+\rho$, since $|f_{i+1}|\le1$. Let $z,w$ be the two roots of $X^2-2xX+1$. Both have modulus one and $zw=1$, also at $x=\pm1$. The quantity $d_i=e_{i+1}-ze_i$ satisfies $d_{i+1}=wd_i+\text{defect}_i$, so $|d_i|\le2\varepsilon+i\tau$. Summing from the bound on $e_1$ gives the displayed result. This is the classical three-term cosine recurrence; the bound accounts for the extra uncertainty in the Salié measurement defining its coefficient. [Lean local-defect and stability inequalities](../PrimeFactors/PhaseEvaluation.lean) · [Oliver on error propagation in related recurrences](https://doi.org/10.1093/imamat/20.3.379)

For target error $0<\delta\le1$, taking $\varepsilon,\rho\le\delta/(4R^2)$ suffices for all $0\le j<R$. Postprocessing costs $O(R)$ arithmetic operations on $O(\log (R/\delta))$-bit numbers, plus the cost of writing the outputs. If the desired answer is the full normalized sum, add the public cosine and scale the accuracy accordingly. With the direct evaluator the three passes cost at most $3\varphi(N)$ unit terms after a single public unit-table construction. Computing each normalized term’s unscaled trigonometric value to error $O(\varepsilon/\sqrt N)$ is sufficient by the triangle inequality. The same three requests can use the existing contraction evaluator. This amortizes evaluation on long progressions. The cost of obtaining the seed readings on a general 2,048-bit product remains open in practice. [Contraction evaluator and its bit-operation bound](counting-salie-phases.md)

The guard bits matter even in exact-arithmetic extrapolation from uncertain data. In the ordinary cosine family $T=0$, compare angular steps zero and $\pi/j$. Their step cosines differ by at most $\pi^2/(2j^2)$, whereas their outputs at index $j$ differ by two. This example explains the quadratic worst-case sensitivity of the recurrence interface over real phases.

The same batching can provide **pairwise independent random frequencies**. Choose $T,D$ uniformly and independently in $\mathbb Z/N\mathbb Z$. For $i<j$ with $(j-i,N)=1$, the map $(T,D)\mapsto(T+iD,T+jD)$ is bijective: subtract the outputs, divide by $j-i$ modulo $N$ and recover the start. Thus every pair in a row of length $R\le\min(p,q)$ is independent and uniform, before any gcd shortcut. For example, a bounded real statistic $|g(t)|\le1$ can be averaged over $g(t_j)c_{t_j}$ with variance at most $1/R$ from the exact cosines, plus at most $\delta$ absolute error in the mean from approximate readings. Once $T,D$ are chosen, the whole row is fixed. This distinction matters for a reduction that must choose subsequent queries after seeing earlier answers. [Checked affine bijection](../PrimeFactors/PhaseEvaluation.lean) · [Weak prediction at chosen inputs](predicting-random-salie-signs.md)

## The 89 fixed inverse-prime readings

There is a one-seed construction tailored to the actual CRT schedule. For any group of its primes let $L=\prod_i\ell_i$, $U=L^{-1}\bmod N$ and $k_i=L/\ell_i$. A nonunit gcd during setup already gives a factor. Otherwise $k_iU\equiv\ell_i^{-1}\pmod N$, so $c_{\ell_i^{-1}}=T_{k_i}(c_U)$, where $T_k(\cos\theta)=\cos(k\theta)$. Uniformly on $[-1,1]$, $|T_k(x)-T_k(y)|\le k^2|x-y|$. This follows from the cosine difference formula and $|\sin(k\theta)|\le k|\sin\theta|$. The derivative at one is $k^2$, so this loss can occur in the real scalar interpolation problem. [Lean multiple-angle bound](../PrimeFactors/PhaseEvaluation.lean) · [Fixed inverse-prime schedule](recovering-residues-from-sums.md#how-much-precision-buys-one-fewer-reading)

Write $K=\max_i k_i$. For absolute error $2^{-b}$ in each **hidden cosine**, it suffices to obtain $c_U$ within $2^{-P}$, where

$$ P=b+\lceil\log_2(K^2)\rceil+1. $$

Clip the reading to $[-1,1]$ and evaluate $\cos(k_i\arccos(x))$ with the remaining $2^{-b-1}$ numerical error allowance. Only the requested indices need to be evaluated: a certified angle to $O(2^{-b}/K)$ suffices for this last calculation, with polynomial bit work in $b+\log K$ per index. At $b=53$ the largest two scheduled primes need one 100-bit seed, the largest four need 192 bits, the largest eight need 376 bits and all 89 need 4,102 bits. For all 89, $\lceil\log_2(K^2)\rceil=4048$. A group saves full sums when its higher precision is available. For direct summation, its per-term arithmetic must also cover the original $\sqrt N$ normalization. The 53-bit output error is below the decoder’s $1/(64\ell_i^2)$ threshold for each of these primes. It suffices to pass bounded-error hidden cosines to that decoder. Exact agreement with rounding a full sum to a particular dyadic grid is unnecessary, and the bound does not guarantee it at grid boundaries.

The required index size is forced for a short one-seed encoding. If each inverse frequency is a signed multiple of one unit $V$ with absolute index at most $K'$, the signed products $\ell_i j_i$ all equal $V^{-1}$ modulo $N$. When $2K'\max\ell_i<N$, the congruent products are the same nonzero integer. Each prime divides it, so its absolute value is at least $L$ and $K'\ge L/\min\ell_i$. [Lean short-index divisibility lemma](../PrimeFactors/PhaseEvaluation.lean)

Allowing an arbitrary starting frequency does little to shorten the full row. For the 89 unreflected frequencies, put $g=\gcd_i(k_i-k_1)=2$ and $S=(\max k_i-\min k_i)/g$. The **minimum modular progression index span is exactly $S$** for every 2,048-bit input coprime to the schedule. To see this, for any proposed indices $j_i$ satisfying $\ell_i^{-1}\equiv T+j_i D\pmod N$, cross multiply the differences at any two distinct reference indices $a,b$:

$$ (j_i-j_a)(\ell_a-\ell_b)\ell_i\equiv (j_b-j_a)(\ell_a-\ell_i)\ell_b\pmod N. $$

For index span at most $S$, the two sides differ by at most $2S\max\ell_i\,(\max\ell_i-\min\ell_i)$. For the published list that integer has 2,046 bits, strictly below $N$. Hence these are ordinary equalities and the $j_i$ are a rational affine transformation of the $k_i$. The normalized differences $(k_i-k_a)/g$ have gcd one, so the rational slope relative to these normalized differences is a nonzero integer. Their span is therefore at least $S$, attained by $T=U\min k_i$, $D=Ug$ and $j_i=(k_i-\min k_i)/g$. Here $\log_2 S\approx2010.516$. The three-reading uniform rule $\varepsilon,\rho\le2^{-53}/(4(S+1)^2)$ budgets **4,077 hidden fractional bits**. These precision figures concern the displayed interpolation methods and do not give lower bounds for general evaluators.

Allowing each inverse to be reflected preserves a large span bound. Replace each auxiliary by its signed value in the cross-product identity. For span $s$ the absolute difference is now at most $4s(\max\ell_i)^2$. If equality fails over the integers then $s\ge N/(4(\max\ell_i)^2)>2^{1999}$. Otherwise, reducing the equality modulo each $\ell_i$, $i\ne a,b$, shows $\ell_i\mid j_b-j_a$. These 87 distinct primes have product exceeding $2^{1999}$. Thus selecting per-frequency signs still leaves the required row exponentially long at this input size.

## What an exact coefficient table would require

An alternative way to share work across frequencies is to aggregate the original terms by their common phase. Define the integer coefficient

$$
 W_N(s)=\sum_{x\in(\mathbb Z/N\mathbb Z)^\times\, :\, x+x^{-1}=s}\left(\frac{x}{N}\right).
$$

The discrete Fourier transform of this table supplies the unnormalized diagonal sums, using $A=t/2\bmod N$ as frequency. For a regular bin, meaning $(s^2-4,N)=1$, its exact value is

$$
 W_N(s)=
 \begin{cases}
 4\left(\dfrac{s-2}{N}\right),& s^2-4\text{ is a square modulo }N,\\
 0,&\text{otherwise}.
 \end{cases}
$$

Indeed $x+x^{-1}=s$ is equivalent to $x^2-sx+1=0$. Any solution is a unit, with inverse $s-x$. Completing the square gives a bijection with square roots of $s^2-4$ because two is invertible. A unit square has four roots by CRT. On the fibre, $(x-1)^2=(s-2)x$ and $x-1$ is a unit, so all four Jacobi weights equal the same public sign. Factoring the sum prime by prime also gives the exact common sequence at **every** $s$,

$$
 W_N(s)=\sum_{v^2=1\bmod N}\left(\frac{s+2v}{N}\right).
$$

At a prime, the sum is $\chi(s+2)+\chi(s-2)$. The signs agree on a regular occupied fibre and cancel when its discriminant is a nonsquare. At $s=\pm2$ the unique preimage is $\pm1$, giving the identity there as well. Multiplying the two prime identities gives the four shifts. Two are public and the other two involve the same hidden root as the Salié samples.

Suppose a unit $a$ has Jacobi symbol $+1$ and its square class is requested. If $(a-1,N)=1$, compute

$$
 s=2(a+1)(a-1)^{-1}\pmod N,\qquad s^2-4=16a(a-1)^{-2}\pmod N.
$$

The new bin is regular, its discriminant has Jacobi symbol $+1$, and it is occupied exactly when $a$ is a square. If $a=1\bmod N$ the answer is known; a proper gcd with $a-1$ gives the factors and permits ordinary prime-field tests. Conversely, one square-class decision for $s^2-4$ yields the exact regular coefficient, with a negative Jacobi symbol already sufficient to certify zero. Thus on the Jacobi-one promise, a regular-table zero test and quadratic residuosity reduce to each other with at most one query and polynomial bit overhead. This relates the exact table to a standard unresolved problem. It establishes no lower bound on computing selected Fourier values. [Checked change of variable over rings with zero divisors](../PrimeFactors/PhaseEvaluation.lean) · [Goldwasser and Micali’s quadratic-residuosity problem](https://people.csail.mit.edu/silvio/Selected%20Scientific%20Papers/Encryption/Probabilistic_Encryption.pdf)

## Bounded checks

For each row below, the starting frequency, step, length and product are public. The three full normalized seed sums were rounded on a $2^{-22}$ grid, then their concealed cosines were rounded on the same grid. Each subsequent multiplication/subtraction was rounded on that grid. For comparison, a separate direct sum at every output used a $2^{-40}$ grid in the repository’s bounded binary64 evaluator. The discrepancies are observed values. The preceding inequalities give the worst-case bounds under certified input errors. [Direct evaluator](../experiments/divisor_samples.py)

| $N$ | $T$ | $D$ | Outputs | Unit terms for the three seeds | Unit terms for separate sums | Maximum observed hidden-cosine discrepancy |
|---:|---:|---:|---:|---:|---:|---:|
| 667 | 334 | 235 | 16 | 1,848 | 9,856 | $4.41\cdot10^{-7}$ |
| 1,763 | 882 | 592 | 24 | 5,040 | 40,320 | $3.32\cdot10^{-6}$ |

On $N=77$, the change of variable sends $a=4$ to $s=29$, giving coefficient $-4$, and $a=6$ to $s=49$, giving zero. Both inputs have Jacobi symbol $+1$. Enumerating the eight regular square inputs and fifteen regular Jacobi-one nonsquares gave the asserted coefficients throughout. [Kernel-checked occupied and empty fibres](../PrimeFactors/PhaseEvaluation.lean)

For both 667 and 1,763 the small schedule uses auxiliary primes 2, 3, 5 and 7. A single rounded sum supplies the four frequencies through polynomials of degrees 105, 70, 42 and 30. We computed the sum from the product, enclosing each trigonometric term and the square-root normalization with rational bounds. The implementation checks that each rounding decision holds throughout the interval represented by the transmitted value. On 667, 616 unit terms gave the factors 23 and 29, down from 2,464 terms. On 1,763, 1,680 terms gave 41 and 43, down from 6,720. A cap of 615 on 667 produced no complete sum. The unit-membership checks in direct evaluation already encounter the factors. For these tests we used those gcds only to decide which terms belong in the sum. [Certified evaluator](../experiments/salie_seed.py) · [Recorded costs and cap](../benchmarks/salie-seed.json)
