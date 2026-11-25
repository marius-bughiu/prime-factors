# Using whole-number positions to check a wider range

**One equation can now cover 5,359 stretches that our original grid checked separately.** Imagine writing all the possible smaller primes in order and dividing the list into equal pieces within each of two regions. The earlier Chebyshev construction could check two neighboring pieces at once. Our new construction can check 5,359 at the same row count. It still needs a way to choose the right piece. On the two public 2,048-bit examples the new, complete searches would require about $2^{495.45}$ and $2^{496.32}$ locations. We have not run either search. [Complete coverage proof](../PrimeFactors/BinomialDivisorCover.lean) · [Previous two-window construction](two-ranges-with-one-equation.md)

## A difference we could test

For 284,987 we took the odd center 517 and checked the 61 odd integers from 457 to 577. The degree-eight Chebyshev equation missed the height limit. Our binomial equation met it and returned two indices, giving **521 and 547**. Their product is 284,987. This window extends on both sides of the square root, so it can contain both primes. We selected this small input and radius while looking for a difference between the two methods. Ordinary near-square factoring also works well on this particular pair. [Benchmark and checked prime factors](https://marius-bughiu.github.io/prime-factors/#binomial-divisor-window-284987)

On the large inputs we fixed the same public center rule and ran seven-row reductions. At an index radius of $2^{439}$, the centered binomial equations ruled out both chosen intervals. Each contained **$2^{440}+1$ odd positions**. The matched Chebyshev equation also worked on the fresh input. On the crossed input it missed its strict bound, while the binomial equation passed and had no root modulo 13. At radius $2^{440}$ the centered binomial equations missed on both inputs. No factor was found in these large runs. [Fresh exclusion](https://marius-bughiu.github.io/prime-factors/#binomial-divisor-window-fresh-439) · [Crossed exclusion](https://marius-bughiu.github.io/prime-factors/#binomial-divisor-window-crossed-439) · [Wider crossed miss](https://marius-bughiu.github.io/prime-factors/#binomial-divisor-window-crossed-440)

| Input and index radius | Binomial coordinates | Binomial swaps | Chebyshev swaps | Outcome of height tests |
|---|---|---:|---:|---|
| 284,987, radius 30 | One-sided, degree 8 | 53 | 57 | Only binomial passed |
| Fresh, $2^{439}$ | Centered, degree 6 | 1,439 | 1,478 | Both passed |
| Crossed, $2^{439}$ | Centered, degree 6 | 1,477 | 1,465 | Only binomial passed |

The full-size centered reductions took about seven seconds each on the development machine. This is the cost of building and testing one equation. The much wider 24,576-row construction below has only been costed mathematically. Separate downloadable Lean certificates verify the input, endpoints and exclusion on the successful fixtures. [Search code](../experiments/binomial_divisor_window.py) · [Centered certificate checker](../PrimeFactors/CenteredBinomialCertificate.lean)

## Why whole numbers give a stronger bound

An odd divisor in a public range has the form $d=c+2x$ for an **integer** $x$. For any integer $x$, the product of $i$ consecutive integers $x(x-1)\cdots(x-i+1)$ is divisible by $i!$. Consequently $\binom{x}{i}$ is integral even though its leading coefficient is $1/i!$. For example, $x(x-1)/2$ always gives a whole number at an integer position. On $0\le x\le H$ its maximum is $H(H-1)/2$. Each higher degree gives a further factorial in the denominator.

We use $F(x)=\sum_{i=0}^k v_i\binom{x}{i}$ with integer $v_i$. Multiplying by $k!$ gives a polynomial with ordinary integer coefficients. We constrain its Taylor coefficients at a public anchor so that $d^m$ divides $k! F(x)$ whenever $d$ is a divisor at position $x$. A prime $d>k$ is coprime to $k!$. It follows that $d^m$ already divides the integer $F(x)$. The strict bound $|F(x)|<d^m$ forces $F(x)=0$. A nonzero equation of degree $k$ has at most $k$ candidate roots. For negative positions, $|\binom{-t}{i}|=\binom{t+i-1}{i}$ when $t>0$, which gives the centered bound. [Integer values, cancellation and exact lattice index](../PrimeFactors/BinomialDivisorWindow.lean) · [Signed positions](../PrimeFactors/CenteredBinomialDivisorWindow.lean)

When $N$ is coprime to $k!$, the public Taylor congruences have exactly $N^{m(m+1)/2}$ different labels for $m\le k+1$. This matters because simply rewriting the old equations in new coordinates would lose the gain to a change in lattice index. Here the search ranges over the larger space of integer-valued polynomials. In the one-sided case the determinant after scaling is exactly

$$N^{m(m+1)/2}\prod_{i=0}^{k}\binom{H}{i}$$

for $k\le H$. Lean proves that the Taylor labels are all attained. In the executable method, the $i$-th row has diagonal entry $N^{\max(m-i,0)}$. Working down the Taylor coefficients determines the needed lower entries modulo their public powers of $N$. Each diagonal coefficient of the cleared binomial polynomial is $k!/i!$, which is invertible in these congruences. Every returned row is checked again. If the public denominator shares a proper factor with $N$, a gcd can already give a split. [Index proof](../PrimeFactors/BinomialDivisorWindow.lean) · [Row construction](../experiments/binomial_divisor_window.py)

## How far this moves the complete search

For $r=24{,}576$, the verified factorial bound is

$$\prod_{i=0}^{r-1} i! \ \ge\ 5360^{r(r-1)/2}.$$

Combine this with $\binom{H}{i} \le H^i/i!$. The one-sided binomial weights for $H=5360U$ now fit within the earlier monomial budget for radius $U$. Centering the basis gives a signed radius of $5359U$ because $24{,}575\le U$. This pays both the finite counting bound and the numerical sufficient inequality for the classical LLL first-vector guarantee. The Lean proof uses a table of small integer thresholds to certify the factorial comparison without constructing a product of billions of bits. [Factorial and determinant budgets](../PrimeFactors/BinomialDivisorScale.lean) · [Earlier budgets](../PrimeFactors/FeasibleDivisorCover.lean)

Use the same two public regions as before and group 5,359 old addresses per equation. If a region had $a$ addresses, the new count is $\lceil a/5359\rceil$, including the final partial block. Together the two regions have **fewer than $2^{497}$ locations** for every 2,048-bit product of two 1,024-bit primes. The proof supplies a location and a root for every possible smaller prime. It does not supply an efficient way to calculate that location from $N$. Constructing and solving an equation at each of these locations would still be infeasible. This is a finite improvement for one family of searches. General-purpose deterministic factoring has a stronger known asymptotic bound. [Grid and control counts](../PrimeFactors/BinomialDivisorCover.lean) · [Harvey and Hittmeir](https://arxiv.org/abs/2105.11105)

At the smaller degree of 128 we can combine the factorial gain with Chebyshev bounds by rounding lower coefficients. One prescribed window can then contain $2^{514}+1$ odd positions by a finite existence proof. The numerical LLL inequality is checked at $2^{513}+1$ positions under the independent input bounds. Neither high-degree search was run. The use of binomial polynomials in lattice methods and restrictions on their attainable exponents have precedents in the literature. Our results concern these finite unknown-divisor windows. [Degree-128 construction](rounding-chebyshev-into-binomial-coordinates.md) · [Chinburg, Hemenway, Heninger and Scherr](https://arxiv.org/abs/1605.08065)

## What clue would select the right window?

The product of the two finite Euler factors gives a boundary reading called $B(1)$. Suppose we are given an estimate of this real number. There is a separation test we can perform with the estimate and $N$ alone. If the inferred lower bound on half the logarithm of the ratio $q/p$ is at least $1/8$, an absolute error of at most $2^{-502}$ suffices to choose one centered binomial window containing the requested prime. We may ask for either prime. At that location one polynomial has at most 24,575 possible integer roots. The previous sufficient error bound was $2^{-516}$, so the wider window tolerates 16,384 times as much error under this separation test. [Selection theorem](../PrimeFactors/BinomialAnalyticWindow.lean) · [Earlier boundary result](what-the-product-says-about-the-window.md#how-precise-would-a-clue-have-to-be)

Producing the reading from $N$ at that precision remains open. The pinned RH repository’s Dirichlet statements concern zero locations and nonvanishing. They do not give a computation of $B(1)$ at the required precision. The implication from a supplied reading to a factor window uses the finite Euler-factor identity and elementary real inequalities. [Definition of the reading](reading-the-boundary.md) · [Pinned Dirichlet statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab/src/Statements.lean)

The formalization imports Mathlib’s falling-factorial polynomials and polynomial interpolation under its Apache 2.0 license. The finite budgets, grid proof and experimental searches are project code. [Pinned Mathlib source](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/RingTheory/Polynomial/Pochhammer.lean) · [Mathlib license](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/LICENSE)
