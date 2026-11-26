# How often can a square-root formula find a factor?

For 156,263, subtract the square of 395 to get 238. The number $238^2-22\cdot238+1=51{,}409$ shares the prime 509 with the input. Dividing gives the other prime, 307. For a uniformly chosen pair of distinct 1,024-bit primes whose product has 2,048 bits, this calculation succeeds on **fewer than one pair in $2^{1004}$**. The proof counts the pairs on which it could succeed, including the possibility of finding either prime. [Worked example](choosing-a-quartic-width-from-the-product.md) · [Lean bounds for the two formulas](../PrimeFactors/SquareRootFormulaExamples.lean)

## What the product contributes

Write $N=pq$, $t=\lfloor\sqrt N\rfloor$, and $r=N-t^2$. Consider any fixed formula $F(N,t)$ made from integers, addition, subtraction and multiplication. It may use $r$, vary the width of the block with the product, or have enormous coefficients. Its proposed factor is the gcd of $F(N,t)$ with $N$. At either hidden prime, $N$ is zero. Consequently the single polynomial $P(T)=F(0,T)$ describes **every possible zero** of the formula modulo that prime. The equality holds modulo $N$ itself. A formula with $P=0$ always gives the whole product. For division by an invertible denominator modulo $N$, the same reduction applies to the numerator. An attempted inversion that already gives a proper divisor is a separate success of the denominator test. [Reduction, primitive part and division](../PrimeFactors/SquareRootPolynomialFormula.lean)

Why can't a handful of these zeros cover many products? Fix one prime $p$ and let its partner vary. The square root stays inside the interval for 1,024-bit integers. That interval has length at most $p$, so each residue of $t$ modulo $p$ corresponds to at most one actual integer $t$. For this fixed $t$, $t^2\le pq<(t+1)^2$ leaves at most two **odd** values of $q$. A polynomial of degree $d$ that stays nonzero as a polynomial modulo $p$ has at most $d$ roots there. These two elementary counts apply to the actual square root of each product. [Partner count](../PrimeFactors/SquareRootShiftPartners.lean)

One detail matters when the coefficients are large. Their common divisor, the *content* of $P$, may itself contain some 1,024-bit primes, making all coefficients vanish modulo those primes. If any one nonzero coefficient has at most $L$ bits, the number $e$ of such primes satisfies $1023e<L$. Their product divides that coefficient. Counting them separately, the number of pairs a test can split is at most $(2d+e)$ times the number of 1,024-bit primes. Combining this count with the repository's unconditional lower bound on the number of eligible pairs gives the following two finite results. [Content and population proofs](../PrimeFactors/SquareRootFormulaPopulation.lean) · [Prime-count normalization](../PrimeFactors/SquareRootPhasePopulation.lean)

* A single polynomial with specialized degree at most $2^{32}$ and **one** nonzero specialized coefficient fitting in 1,048,576 bits splits fewer than one pair in $2^{974}$. Its other coefficients and its degree in $N$ may be arbitrarily large.
* Even choosing among $2^{30}$ such formulas after inspecting the full product, or trying every one of them, reaches fewer than one pair in $2^{944}$. This bound covers a previously fixed menu and counts successes on either prime.

The degree refers to the polynomial after setting $N=0$. Repeated squaring can produce a high degree with a short computation. The theorem also leaves open methods that use other information about the product, including new integer divisions, varying exponents and further integer square roots.

## Two choices suggested by the block formula

For odd block width $m$, the earlier search used the arithmetic expression $Q_m(t)=48t^4-24(1+m^2)t^2+(m^2-1)^3$. Holding $m$ fixed and adding an offset to $t$ leaves at most four possible roots per prime. A nonempty menu of $J$ such settings finds a proper factor on fewer than $J/2^{1004}$ of the eligible pairs. At a fixed width and zero offset the even powers of $t$ improve the bound to $1/2^{1005}$. These statements concern the gcd of the polynomial value itself. [Fixed widths and offsets](../PrimeFactors/BlockProbePopulation.lean)

Choosing the width equal to $t$ gives $(t^2-1)(t^4+22t^2+1)$. When $t$ is even, $t+N$ is odd and gives the same coefficient modulo the odd product. The second factor reduces to $r^2-22r+1$, the test that found 509. Another choice is $m=2r+3$. For 34,756,699 this gives $t=5895$, $r=5674$ and $m=11{,}351$. The coefficient gcd returns 4,483, and division gives 7,753. This second formula has specialized degree 12 and succeeds on fewer than one eligible pair in $2^{1003}$. Evaluating the coefficient requires just the public numbers in the formula, even for a very large width. [Kernel-checked readouts and bounds](../PrimeFactors/SquareRootFormulaExamples.lean) · [Benchmark inputs and expected readouts](../benchmarks/adaptive-quartic.json)

The table counts all products of two distinct primes of the given width whose product has twice that width. Each comparison receives the product alone. We tried the four tests after the same nine consecutive candidates around $t$ all returned gcd one.

| Bits per prime | Products passing the nine-position check | Adjacent integer | Fixed width 3 | $r^2-22r+1$ | Width $2r+3$ |
|---:|---:|---:|---:|---:|---:|
| 9 | 510 | 12 | 3 | 3 | 3 |
| 10 | 1,667 | 14 | 2 | 4 | 3 |
| 11 | 5,436 | 33 | 8 | 2 | 6 |
| 12 | 19,403 | 48 | 10 | 12 | 11 |
| 13 | 64,473 | 78 | 16 | 15 | 20 |

The four sets of successes were disjoint at every width. The two varying-width tests recovered some pairs that the other tests missed, and checking the adjacent integer split more products at every width. Both varying-width formulas missed both 2,048-bit controls. The independently generated control remains unresolved from its product alone. [Reproduce the census](../experiments/square_root_formula.py) · [Control provenance](certified-fresh-control.md)
