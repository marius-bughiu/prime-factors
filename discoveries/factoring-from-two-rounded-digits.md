# Can the digits of a product reveal both primes?

We recovered two 1,024-bit primes from their product by trying 129 square roots. A second product took 996. We deliberately chose all four primes to make this possible. Two earlier 2,048-bit products each survived 41,472 guesses without revealing a factor. For someone supplying their own product of two random primes, we still have no practical general solution. [Exact inputs and expected factors](../research/radix-carry-controls.json) · [Benchmark cases](../benchmarks/radix-carries.json)

## Try it on 143

Suppose you know only 143. Pick a base of 8. Dividing 143 by 64 and by 8 gives rounded answers of 2 and 18. Try adjusting the first answer from 2 to 1, and the second from 18 to 16. Then form the proposed sum $1\times8+16=24$. Two integers with sum 24 and product 143 differ by $\sqrt{24^2-4\times143}=2$. They must be 11 and 13. Both adjustments came from a short list the search tries on every input.

The interesting part at full size is that the square root can reveal the primes even when it gives the difference between *multiples* of those primes. The search can recover a prime from one of those multiples without guessing what either multiplier was. [Recovery theorem and checked small example](../PrimeFactors/PredictedTraceCarries.lean)

## What the product determines

Pick a base $D>0$. Write the factors as $p=AD+x$ and $q=BD+y$, allowing the remainders $x,y$ to be negative. The search knows $N=pq$ and $D$. Define $Q$ as $N/D$ rounded to the nearest integer and $C_0$ as $N/D^2$ rounded the same way, with half ties rounded upward. Try two small integer corrections $h,k$ and set

$$C=C_0+h,\qquad T=CD+Q-k,\qquad \Delta=T^2-4CN.$$

If the two trial values happen to equal $AB-C_0$ and the nearest integer to $xy/D$, then $C=AB$ and $T=Bp+Aq$. This follows by expanding $N=D(Bp+Aq-ABD)+xy$. The square root of $\Delta$ is then $|Bp-Aq|$. When $AB$ is coprime to $N$, the greatest common divisor of $N$ and $(T+\sqrt{\Delta})/2$ gives one of its factors. Every reported proper divisor is valid even if the square came from a different relationship. [Signed rounding, recovery and soundness](../PrimeFactors/PredictedTraceCarries.lean)

For a 2,048-bit input the experiment tries $D=2^e$ for each $e$ from 513 through 1,024. At each base it makes at most $(2H+1)(2K+1)$ guesses when the respective corrections range from $-H$ to $H$ and $-K$ to $K$. A negative discriminant costs a guess and can skip the square-root test. The search receives only the product and the two limits. [Search implementation](../experiments/radix_carries.py)

| Input | Limits $H,K$ | Guesses tried | Integer square roots | Result |
|---|---:|---:|---:|---|
| First constructed product | 0, 0 | 192 | 129 | Both primes recovered |
| Second constructed product | 1, 1 | 1,728 | 996 | Both primes recovered |
| Same second product | 0, 0 | 512 | 439 | Whole product unresolved |
| Earlier comparison, fresh | 4, 4 | 41,472 | 34,591 | Whole product unresolved |
| Earlier comparison, crossed | 4, 4 | 41,472 | 34,056 | Whole product unresolved |

Both successful searches reached base $2^{704}$. The second used corrections $(1,1)$. Scanning the whole range with either correction fixed at zero and the other allowed to vary from $-1$ to $1$ also missed. Each positive benchmark has two Lean certificates. One replays the winning guesses, and the other checks the primality of both recovered numbers and their product. [First example](https://marius-bughiu.github.io/prime-factors/#radix-carry-zero-2048) · [Second example](https://marius-bughiu.github.io/prime-factors/#radix-carry-nonzero-2048)

We selected primes just above $13\cdot2^{1020}$ and $15\cdot2^{1020}$ with remainders at the chosen base that give the desired corrections. We also planted a large prime power in each prime's predecessor so Lean could certify primality economically. The inputs share no prime. We screened the second input for failure when either correction was fixed at zero. For the primitive weights of the two examples, their true weighted sums are respectively 609,853,990,796,593,837 and 2,625,845,679,704,917,018 above the rounded-up lower bound $2\sqrt{CN}$. The rounded product digits let us try these distant sums directly. These figures measure distance along these particular weighted sums. [Control construction and selection](../experiments/radix_carry_control.py)

## How many ordinary products could it reach?

A successful guess with $|k|\le4$ forces the factors to satisfy $|(p-AD)(q-BD)|\le 4.5D$ for some integers $A,B$. This holds even for a lucky square from an unexpected pair of weights. At least one prime must therefore lie close to a multiple of $D$. Counting all such neighborhoods at all 512 tested bases bounds the chance of any success by **less than one in $2^{234}$** for uniformly chosen distinct 1,024-bit primes conditioned on a 2,048-bit product. The bound even permits an unlimited first correction chosen after seeing the entire product. The counting proof in Lean takes an explicit prime-population inequality as a hypothesis. Its justification uses published unconditional prime counts. [Population proof](../PrimeFactors/ShiftedEndpointPopulation.lean) · [Prime-count derivation](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)

Trying smaller powers of two also leaves the bound below one in $2^{234}$ when both corrections at those smaller powers lie between $-4$ and $4$. The proof covers every power from $2^1$ through $2^{1024}$. [Smaller-base proof](../PrimeFactors/ShiftedSmallRadices.lean)

Two related tests show where some of the ambiguity remains. Modulo $2^{640}$, covering every odd first-factor residue by guessing exact nonzero products of two offsets of absolute product below $2^{1280}$ needs more than $2^{471}$ guesses, even if the origins can be translated. That statement counts local possibilities. A rule using additional information about the actual prime pair could avoid covering them all. [Exact lift bound](../PrimeFactors/ShiftedEndpointProduct.lean)

A binary square test can sometimes eliminate a whole interval. For $2{,}022{,}961=1013\times1997$, one test modulo 256 rules out every possible divisor from 1,018 through 1,209. We chose this example for its long run of failed tests. Lean also proves a sharp limit. For every odd product $N$, every 62 consecutive midpoint guesses include one $m$ for which $m^2-N$ is a square modulo *every* power of two. Modular square tests alone cannot reject that guess, even though an actual factor requires an integer square. [Interval proof, exact sharp bounds and example](../PrimeFactors/ShiftedDyadicMidpoints.lean)

## Related mathematics

Eoin Mackall studies how factoring the polynomial formed from the ordinary base-$D$ digits of $N$ can yield divisors of $N$ by evaluation. The quadratic case is particularly close to this calculation. Here the trial polynomial has signed coefficients $C$, $Q-k-2CD$ and $N-D(Q-k)$. At the correct carries it equals $(AX+x)(BX+y)$ in the variable $X$. The experiment varies the two carries and checks the resulting square directly. The implementation and Lean proofs were written independently. [Mackall, *A factorization algorithm based on Cohn's irreducibility criterion*, Remark 3.2 and Example 3.3](https://eoinmackall.github.io/files/papers/factorization.pdf)

The released RH and Dirichlet results concern the distribution of primes and zeros of analytic functions. Our earlier work uses such estimates to count primes in candidate intervals. The digit formula here uses integer arithmetic throughout. We have no derivation from RH that predicts the missing corrections for an individual input. [Upstream theorem statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Statements.lean) · [Project's analytic assumptions](../docs/research.md)
