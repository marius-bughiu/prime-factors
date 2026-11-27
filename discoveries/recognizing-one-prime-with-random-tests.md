# A test can identify one prime without telling us where to find it

For any product of two distinct 1,024-bit primes, we can write down 1,100 tests using only the product and random numbers. The smaller prime always passes. With independent uniform choices, the chance that **any other eligible prime** passes them all is at most $2^{-76}$. Lean proves this for every such product without a hypothesis about the distribution of primes. **We still cannot use the tests to find an unknown 1,024-bit prime efficiently.** Checking a proposed prime by dividing the product is already easy. [Single-test proof](../PrimeFactors/AffinePrimeSign.lean) · [Joint probability and uniqueness](../PrimeFactors/PrimeSignIsolation.lean)

For example, take 77. Its odd prime candidates up to the square root are 3, 5 and 7. Pick the test number $1-4\times77=-307$. Upon division by 3, 5 and 7 it leaves remainders 2, 3 and 1. Only the last remainder is a nonzero square at its prime. The test picks out 7 once the three candidates have been listed.

## Why it works on every product

For a public product $N$, draw $r$ uniformly from the integers $0,\ldots,N-1$. A prime candidate $\ell$ passes if $1-4Nr$ is a **nonzero** square modulo $\ell$. At a true divisor this remainder is always 1. At any false odd prime $\ell$, multiplication by $-4N$ followed by addition of 1 permutes the remainders modulo $\ell$. Exactly $(\ell-1)/2$ of them pass.

The draws need not cover an integer number of periods modulo $\ell$. Write $Q=\lfloor N/\ell\rfloor$. Each residue occurs at most $Q+1$ times. Since $\ell^2\le N$ for a candidate for the smaller prime, $Q\ge\ell$ and $(\ell-1)(Q+1)<N$. Thus fewer than half of all draws pass a fixed false prime, even at the incomplete end of the interval. The gates for different candidate primes may be correlated.

After $k$ independent draws with replacement, each false prime has probability at most $2^{-k}$ of surviving. There are fewer than $2^{1024}$ candidate primes below $2^{1024}$. Adding their individual probabilities gives the claimed bound for $k=1100$. It also gives $2^{-64}$ with 1,088 tests. This proof even allows testing all odd primes up to $\sqrt N$ and the size cap, without a lower cutoff. The only actual prime divisor in that range is the smaller prime.

## How much work did it save?

We enumerated all primes in the possible factor interval on the first input of each of two previously used independent samples. All methods received just the product and factor width. The fixed SHAKE256 labels make these runs reproducible. The theorem's probability refers to genuinely independent uniform draws. [Deterministic data and timing samples](../research/affine-prime-signs.json)

| Bits per prime | Primes before tests | Tests until one survived | Symbols evaluated to reach one | Verified factors | Direct prime division | Time to isolate one prime |
|---|---:|---:|---:|---|---:|---:|
| 20 | 9,995 | 12 | 19,893 | 837,533 × 942,583 | 2.70 ms | 20.64 ms |
| 24 | 61,477 | 20 | 123,177 | 15,230,737 × 16,163,387 | 18.52 ms | 151.86 ms |

These are median CPU times including generation of primes, labels where applicable, and the search. A third implementation visited primes in ascending order, stopping after the first passing prime actually divided the product. It took 13.43 ms and 85.55 ms. Both small results have Lean factorization certificates. For the two 2,048-bit products we generated and hashed the 1,100 labels in under 2 ms each. We visited **zero** full-size candidates. Neither fixed panel has been individually certified to isolate a single prime. [Reproduce the experiment](../experiments/affine_prime_signs.py)

The missing step is to generate a surviving prime directly from the public tests at lower cost than ordinary factor discovery. The earlier prime-ideal result addresses another question, giving a two-sided bound for a fixed panel of 400 tests on a specified input. [Counting the survivors of fixed tests](how-many-primes-pass-hundreds-of-tests.md)

## Why the theorem specifies prime candidates

Extending the test to every odd integer by using the Jacobi symbol leaves a large family of composites. For an odd prime $t$ coprime to a label $z=1-4Nr$, the symbol at $t^2$ is $(z/t)^2=1$. On each full-size input, **more than $2^{498}$ distinct prime squares** in the physical factor interval pass every label, for every choice of 1,100 draws. A perfect-square check can discard this whole family.

To count them, take $2^{511}\le t\le 2^{512}$ in a shorter interval whose squares lie inside the factor window. Each nonzero $|z|<2^{4098}$ has at most eight prime divisors that large. Across 1,100 labels at most 8,800 base primes can be excluded. Dusart's explicit, unconditional prime-count estimates give more than $2^{498}+8{,}800$ primes in each specified base interval. Lean checks the interval inclusions and the count from the stated published inequalities. [Square-symbol proof](../PrimeFactors/SquarePrimeDecoys.lean) · [Both full-size intervals](../PrimeFactors/FullSizeSquareDecoys.lean) · [Dusart, equation (6.6)](https://arxiv.org/pdf/1002.0442#page=9)

## Removing squares also removes the need to test candidate primality

Consider all odd nonsquares of the correct bit width in the physical factor interval. A false candidate $c$ is coprime to $N=pq$. Indeed $c\le\sqrt N\le q$ and $c<2p$, so no multiple of either prime other than the true smaller prime fits. At an odd nonsquare modulus the Jacobi symbol is a nonprincipal character. Some prime dividing $c$ occurs with odd multiplicity. Choosing a nonresidue at that prime and 1 at the other prime factors by the Chinese remainder theorem gives a unit of negative sign. Multiplying by it pairs all positive and negative units, so exactly $\varphi(c)/2$ remainders pass. The affine permutation and incomplete-period argument above now applies to composite $c$ as well. There are only $2^{1022}$ odd 1,024-bit integers, even before applying the interval and square tests. Thus 1,100 independent draws leave the true smaller factor as the only surviving integer in this set except with probability at most $2^{-78}$. The bound holds for each input individually. [Nonprincipal character and single-draw bound](../PrimeFactors/AffineNonsquareSign.lean) · [All-integer uniqueness](../PrimeFactors/NonsquareSignIsolation.lean)

For the same two small products this version started with 67,779 and 508,256 odd nonsquares. They narrowed to one in 18 and 20 tests, after 132,011 and 842,265 Jacobi evaluations respectively. An ascending divisibility search over those integers took 12 ms and 81 ms. Isolating the unique survivor took 173 ms and 1.33 seconds. Each is a single CPU timing including setup. [Complete counts and experimental settings](../research/affine-prime-signs.json)

## An exact formula and the cost of evaluating it

Let $C$ be the public set of odd nonsquares in the possible factor interval, $z_i=1-4Nr_i$, and $J_i(x)=(z_i/x)$. If the only survivor is $p$, then

$$p=2^{-k}\sum_{x\in C}x\prod_{i=1}^k\big(J_i(x)+J_i(x)^2\big).$$

Each bracket is 2 for a pass and 0 otherwise, including when the symbol vanishes. At $N=77$, the weighted sum for the one-test example is 14 and division by 2 gives 7. Expanding the product gives $2^k$ incomplete weighted character sums. Lean checks this expansion using multiplicativity of the Jacobi symbol. Direct evaluation visits the candidate interval. Writing out the full expansion at $k=1100$ produces $2^{1100}$ terms. A faster exact evaluation would be needed for this formula to help recover the full-size factors. [Lean identity and worked example](../PrimeFactors/SignPanelReadout.lean)
