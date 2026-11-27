# Comparing weighted powers at both primes

A search for the factors of an odd product can make a lookup table shared by different choices of weights. For the 18-bit product 154,421, seven weight pairs needed only four distinct entries on one side of the lookup. One match gave the prime factor 503. On the two 2048-bit controls, the table and the remaining search are still far too large for a desktop. [Lean proofs](../PrimeFactors/WeightedGlobalTrace.lean) · [Bounded experiment](../experiments/weighted_global_trace.py)

## A match using only the product

Write $N=pq$ for two distinct odd primes. Choose any unit $u$ modulo $N$, such as 2. For weights $a\le b$, the desired sum is $s=ap+bq$. The search proposes $s$ using only the public product. Harvey's local identity relates $u^s$ to $u^{a+bN}$ modulo $p$. Swapping the roles of the primes gives $u^s=u^{b+aN}$ modulo $q$. Harvey's factoring algorithm uses baby steps, giant steps and polynomial evaluation to batch local collisions. Harvey and Hittmeir later improved its running time. [Harvey, Lemma 2.4 and Algorithms 4.1–4.2](https://arxiv.org/pdf/2010.05450) · [Harvey and Hittmeir](https://arxiv.org/abs/2105.11105) · [Earlier project treatment](farey-weighted-sums.md)

Take $h=(N-1)/2$, $c=a+b$ and $d=b-a$. Compute two units modulo $N$,

$$X=u^{s-(h+1)c},\qquad Y=u^{hd}.$$

A negative exponent means taking the inverse of the corresponding positive power. At the true sum, the first local identity gives $X=Y$ modulo $p$, and the second gives $X=Y^{-1}$ modulo $q$. Both identities therefore give the *same* publicly testable equality modulo $N$,

$$X+X^{-1}=Y+Y^{-1}\pmod N.$$

Every pair of weights with the same difference shares the whole right entry. With the public bounds $Rb\le(R+e)a$ and $ab\le K$, only the gaps from zero through $\lfloor e\lfloor\sqrt K\rfloor/R\rfloor$ need consideration. Once $u^h$ and its inverse are known, each successive right power and its inverse take two modular multiplications in total. A scan can also generate entries only for gaps it encounters.

For any match, $(X-Y)(XY-1)=0$ modulo $N$. If $X=Y$ or $XY=1$ already modulo $N$, the match alone need not give a factor. At a true sum, the public precheck $\gcd(Y^2-1,N)=1$ rules out both cases. Then $\gcd(X-Y,N)$ is a proper divisor. A proper divisor obtained by the precheck itself is also usable. The gap $d=0$ gives $Y=1$ for every base, so the underlying integer-square test still matters. Swapping the two primes interchanges the orientations and leaves the trace equality intact. [Global equality and proper-divisor proof](../PrimeFactors/WeightedGlobalTrace.lean) · [General modular match classifier](../PrimeFactors/TraceFoldedRight.lean)

## What still needs searching

In a narrow square window $4abN\le s^2\le4abN+W^2$ with $W^2<N$, the quotient $\lfloor s^2/N\rfloor$ is exactly $4ab$. Hence $(a+b)^2-\lfloor s^2/N\rfloor=(b-a)^2$. The pair $(c,s)$ determines its sorted weights uniquely. Two different weight assignments never generate the same left indices here. Moreover each proposed $s$ lies between zero and $h$ in the project's 2048-bit rectangle. Consequently the **integer exponent** $s-(h+1)c$ also determines both indices. Any further reuse on this side needs a different mechanism, such as evaluating many distinct exponents together. [Window, exponent and full-width bounds](../PrimeFactors/WeightedGlobalTrace.lean)

On the fresh and crossed controls, the base-two logarithms of the dense right-table upper bounds are 339.49 and 340.82, respectively, rounded to two decimals. The existing weight-window coordinate ceilings have logarithms 679.34 and 680.60. These are size estimates. They establish neither an improvement on Harvey's full algorithm nor a lower bound on every possible batching strategy. [Public inputs and coordinate budgets](../research/rectangular-multiplier-products.json)

## Reproducing the small example

Run `python3 -m experiments.weighted_global_trace`. The 18-bit example was chosen with a factor ratio near $5/3$. The scan receives only $N=154421$, the common prime width 9 and base 2. It visits all seven admissible primitive weight assignments in the public rectangle and checks eight coordinates against their own weight gap. The four occurring gaps are 0, 1, 2 and 4. A second pass indexes the gaps by their trace and tests each left key against the whole table in one lookup. It finds the same single match. For $(a,b)=(3,5)$ and $s=3044$ it gets $X=124284$, $Y=103158$ and a common trace of 124904. The precheck gives 1. The final gcd gives 503, and $154421=503\cdot307$. Lean checks the powers, the traces, the gcd and primality of both factors. The same small example also admits an ordinary square test. [Reproducer](../experiments/weighted_global_trace.py) · [Arithmetic certificate](../PrimeFactors/WeightedGlobalTrace.lean)

## Three methods on the same candidates

The comparison uses base 2, multiplier $k\le64$, and the first two denominator coordinates in each eligible interval. All three methods finish this budget, including after a factor appears. The square method tests $y^2-kN$ once per distinct $(k,y)$ and takes the gcd of $y-x$ and of $y+x$ with $N$ whenever the result is a square $x^2$. The own-gap method compares a candidate only with its assigned $b-a$. The global method hashes all the right traces and checks every matching gap in one lookup per candidate. Both power methods get the same setup gcds. The eight small holdout inputs come from independent prime draws using SHAKE256, seed `weighted-global-trace/v1`, sides `p` and `q` and indices 0 through 7. The program takes only their products and the shared prime width when searching. [Benchmark fixture](../benchmarks/weighted-global-trace.json) · [Generation of the prime draws](../experiments/affine_radix_holdout.py)

| Inputs | Coordinates visited | Row-square splits | Own-gap splits | All-gap splits |
| --- | ---: | ---: | ---: | ---: |
| Eight held-out pairs of 9-bit primes | 51 | 7 | 3 | 3 |
| Fresh 2048-bit control | 4 | 0 | 0 | 0 |
| Crossed 2048-bit control | 12 | 0 | 0 | 0 |

For four holdout inputs the power methods saw an equality with $X=Y$ modulo the whole product. Its gcd was $N$, so it contributed zero splits. The square method recovered both primes on all four of those inputs. All three methods exhausted their budget without a factor on the holdout product 103,127 and on both full-size controls. The fixture records how many coordinates were skipped below the multiplier cap, the full multiplier limit, and the unresolved product for each global-search miss.

**One different gap really can help.** We selected 91,787 retrospectively to test this behavior. Eight coordinates and six gap entries gave no square, no own-gap match and no factor during setup. In row 3, $(a,b)=(1,3)$ and $y=526$ give $s=1052$ and $X=65608$. The entry for gap **4**, while the weights' own gap is **2**, gives $Y=62118$. Both traces equal 36728 modulo 91787, and $\gcd(65608-62118,91787)=349$. A cheaper check also finds this pair. The left candidate $s=1052$ is exactly $4\cdot263$, so $\gcd(s,91787)=263$. Here the weight sum and the matched gap both equal 4. The alternate weights are therefore 0 and 4, and the extra match recovers an ordinary multiple of one prime. Lean verifies $91787=263\cdot349$ with both factors prime. Two further selected diagnostics show why every readout is recorded. At 25,021 an extra gap match gives gcd 1. At 43,621 the precheck alone gives factor 241 before either trace search reads a left coordinate. These selected examples are separate from the eight holdout inputs. [Fixtures and counted readouts](../benchmarks/weighted-global-trace.json) · [Regression tests](../tests/test_weighted_global_trace.py)

**Cost on the full-size inputs.** Each method first pays to form the common candidate schedule, including the ratio bound, weight gcds and integer-square-root interval endpoints. Fresh required two right entries and four left coordinates. Crossed required three right entries and twelve left coordinates. In this implementation each trace method makes one modular-power call, inversion and precheck gcd per right entry, plus one initial base gcd and inversion. Each left coordinate takes one modular-power call, one inversion and one lookup. Every returned match triggers a gcd, including matches that yield 1 or $N$. The global method additionally builds a hash table with one record per right entry. The code counts even the cheap zero-gap power call. The square baseline deduplicates shared row coordinates and uses one integer square root per test with no modular pre-sieve.

In three rotated runs, median CPU times including schedule construction were 0.095 ms for square, 91.0 ms for own-gap and 91.5 ms for global on fresh. On crossed they were 0.156 ms, 252.8 ms and 250.6 ms. Global table and base setup consumed 15.3 ms and 30.2 ms respectively, in addition to the common schedule. These are measurements of the small fixed budget in this implementation. To reproduce the work counts, timings and Lean checks for all eleven recovered pairs, run `python3 -m experiments.weighted_global_trace --panel --repeats 3 --verify`. [Implementation](../experiments/weighted_global_trace.py) · [Expected outcomes](../benchmarks/weighted-global-trace.json)
