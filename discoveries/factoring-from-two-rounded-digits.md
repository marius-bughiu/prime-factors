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

A successful guess with $|k|≤4$ forces $|(p-AD)(q-BD)|≤4.5D$ for some positive integers $A,B$. Even a lucky square from an unexpected pair of weights must satisfy this condition. Count both distances together. If the first distance is at least $2^i$, the second is at most $4.5D/2^i$. Summing these rectangles across all 512 tested bases bounds the fraction of successful target pairs by **less than one in $2^{468}$**. The proof even permits an unlimited first correction chosen after seeing the entire product. [Why an accidental match also requires two small distances](../PrimeFactors/ShiftedEndpointPopulation.lean) · [Count of pairs of distances](../PrimeFactors/CarryRemainderPairs.lean)

The same bound holds if we add all smaller powers of two, down to 2, and let each of their two corrections range from $-4$ to $4$. The combined count is under $2^{1553}$ pairs, including both orientations. To interpret it as a probability, we select two distinct 1,024-bit primes uniformly, order them by size and condition on a 2,048-bit product. There are at least $2^{2021}$ eligible unordered pairs. This last inequality is the explicit analytic premise of the Lean fraction theorem. [Smaller bases](../PrimeFactors/ShiftedSmallRadices.lean) · [All 1,024 powers together](../PrimeFactors/CarryRadixCoverage.lean)

Could reading more digits tell us which correction to try, even if it is large? At base $D=2^{704}$, let any rule read the lowest 1,023 bits of the product and propose $J$ lower corrections. For each proposal let $w=N-DQ+Dk$, its predicted signed product of the two remainders. If every proposed $|w|<2^{1406}$, the success fraction is less than $J/2^{501}$. This size limit is automatic for remainders measured from their nearest multiples of $D$. A proposed nonzero $w$ restricts the first factor's remainder to a signed divisor of $w$. Once the first factor is fixed, the low bits of the product determine the second factor modulo $2^{1023}$. Counting these possibilities also covers accidental hits with arbitrary weights. For a small illustration, $41×59$ and $47×61$ share their lowest five bits, yet their true lower corrections at base 16 are 2 and 0. [Low-digit prediction theorem and example](../PrimeFactors/LowBitsCarryMenu.lean) · [Open extension using both ends of the product](predicting-a-carry-from-both-ends.md)

For the two population estimates write $X=2^{1023}$. The project's prime-count derivation gives more than $0.22X/\log X$ primes beyond the first in $[\sqrt{2}X,2X)$. Any two distinct primes there form an eligible pair. Using $\log X<710$ gives $X^2<21{,}000{,}000$ times the number of eligible pairs, and in particular that number exceeds $2^{2021}$. Lean proves the fractions from the corresponding numerical premises. The prime estimates used on paper are unconditional. [Derivation and primary source](stride-budget.md#an-explicit-bound-at-exactly-2048-bits)

Two related tests show where some of the ambiguity remains. Modulo $2^{640}$, covering every odd first-factor residue by guessing exact nonzero products of two offsets of absolute product below $2^{1280}$ needs more than $2^{471}$ guesses, even if the origins can be translated. That statement counts local possibilities. A rule using additional information about the actual prime pair could avoid covering them all. [Exact lift bound](../PrimeFactors/ShiftedEndpointProduct.lean)

A binary square test can sometimes eliminate a whole interval. For $2{,}022{,}961=1013\times1997$, one test modulo 256 rules out every possible divisor from 1,018 through 1,209. We chose this example for its long run of failed tests. Lean also proves a sharp limit. For every odd product $N$, every 62 consecutive midpoint guesses include one $m$ for which $m^2-N$ is a square modulo *every* power of two. Modular square tests alone cannot reject that guess, even though an actual factor requires an integer square. [Interval proof, exact sharp bounds and example](../PrimeFactors/ShiftedDyadicMidpoints.lean)

## Related mathematics

Eoin Mackall studies how factoring the polynomial formed from the ordinary base-$D$ digits of $N$ can yield divisors of $N$ by evaluation. The quadratic case is particularly close to this calculation. Here the trial polynomial has signed coefficients $C$, $Q-k-2CD$ and $N-D(Q-k)$. At the correct carries it equals $(AX+x)(BX+y)$ in the variable $X$. The experiment varies the two carries and checks the resulting square directly. On his published input $207{,}314{,}063{,}849$, we checked that base 40,098 with corrections $(-1,1)$ recovers 323,131 and 641,579. On the same input our automatic choice of powers of two missed in all 810 guesses. Selecting the base can decide whether the method succeeds. The implementation and Lean proofs were written independently. [Checked external example](../PrimeFactors/PredictedTraceCarries.lean) · [Mackall, *A factorization algorithm based on Cohn's irreducibility criterion*, Remark 3.2 and Example 3.3](https://eoinmackall.github.io/files/papers/factorization.pdf)

The released RH and Dirichlet results concern the distribution of primes and zeros of analytic functions. Our earlier work uses such estimates to count primes in candidate intervals. The digit formula here uses integer arithmetic throughout. We have no derivation from RH that predicts the missing corrections for an individual input. [Upstream theorem statements](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Statements.lean) · [Project's analytic assumptions](../docs/research.md)
