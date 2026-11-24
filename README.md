# Prime Factors

What information about two unknown primes can be recovered cheaply from their product alone? This project studies classical integer factorization in Lean 4. A motivating case is a 2,048-bit integer $N=pq$ with two 1,024-bit primes and no supplied relation between them. Progress can be a constructive formula, a proved reduction in the work needed to find a factor, or a proof that a proposed relation leaves too many candidates. [Current research](discoveries/character-conjectures.md) · [Project progress](https://marius-bughiu.github.io/prime-factors/)

## A fifth structured 2048-bit factorization

For balanced primes, if the totient $(p-1)(q-1)$ is $d$ times a square, the product and $d$ determine the factor sum by one integer square root. Trying $d=1$ through $6$ recovered two 1024-bit primes 38.76% apart from their product alone. Stopping at five leaves the input unresolved. A counting argument bounds how often a small squarefree part occurs, even before imposing primality. [Formula, proof and construction](discoveries/discriminant-strides.md) · [Benchmark and controls](benchmarks/predecessor-square.json)

There are also infinitely many separated prime pairs whose totients lie one of 49 fixed square offsets below a square, even as their squarefree parts grow without bound. Testing the corrections from the product found both factors of a 92-bit input in two discriminant tests. The existence proof uses an unconditional theorem on prime values of linear forms. Lean checks the decoder. [Infinite family and weighted Fermat comparison](discoveries/near-square-families.md)

For a general balanced pair, suppose the totient lies within $E$ of $d y^2$ for some $d\le L$. At a fixed relative gap, even errors up to a constant times $N^{1/4}$ still permit a paper reduction to $O(L)$ polynomial-time small-root computations. Lean bounds the square-root candidates and the interval for the larger prime. For polylogarithmic $L$, a counting argument bounds the fraction of balanced pairs meeting this promise. [Error bounds, cost and rarity](discoveries/approximate-totient-squares.md)

## A fourth structured 2048-bit factorization

A Fermat search can advance by the square of a divisor of the half-gap. Trying successive powers of five split a 2048-bit product with primes 19.4% apart in **438 midpoint tests and 4,375 modular lifting tests**. The search received only the product and fixed budgets. Both prime predecessors are twice a prime. A control of the same size exhausts the budget. [Search bound, construction and certificate](discoveries/smooth-factor-gaps.md)

For primes sampled from $[X,2X]$, we also derive how often a test of this kind succeeds. Testing every auxiliary prime between $\sqrt X$ and $X^{3/4}$ recovers a proportion approaching $\log(3/2)$, about 40.55%. The cost grows as $N^{3/8+o(1)}$. The known deterministic one-fifth method is asymptotically faster and covers every input. Small experiments compare both square-test counts and elapsed time with Fermat. [Population theorem and measurements](discoveries/gap-search-frequency.md)

There is a sharp limit for this style of search. If a list of moduli and depths is fixed before seeing the product and reserves $T$ midpoint tests, its best possible success probability among random prime pairs in $[X,2X)$ is of order $T/\sqrt X$ for $1\le T\le X^{1/2-\epsilon}$ and fixed $0<\epsilon<1/2$. The proof constructs lists attaining that order. A finite bound shows that even $2^{40}$ reserved tests cover less than a $2^{-461}$ fraction of the exactly 2048-bit products in this model. [Optimal coverage theorem and scope](discoveries/stride-budget.md)

If each product instead chooses its own list by reading up to 1,024 bits from its two ends, even an optimally trained table with $2^{40}$ reserved tests succeeds on less than a $2^{-441}$ fraction of the exactly 2048-bit population. Lean verifies the bound on the number of integer pairs in one table entry. A paper proof counts the prime pairs and gives sharp asymptotics when a fixed proportion fewer bits are read. [Finite bound and exhaustive small tables](discoveries/product-prefix-and-suffix.md) · [Sharp asymptotic theorem](discoveries/sieved-product-advice.md) · [Selection by other residues and Dirichlet GRH](discoveries/conditional-strides.md)

A change *within* each search still saves work. Reading a digit already computed during square-root lifting reduces 18,546 full square tests to 7,468 on the power-of-five fixture at the same 128-index window. Both searches recover the same primes. The control and the one-index comparison show how this depends on the input and the budget. [Proof and measurements](discoveries/stride-wheel.md)

## One 512-bit count suffices for a 2048-bit semiprime

Given only an $n$-bit product $N=pq$ of two distinct odd primes, set $k=\lceil n/4\rceil$. Count triples satisfying $1<x\le y$, $xy=N$, and $0\le t<y\bmod 2^k$. The count is exactly the low $k$ bits of the larger prime. A published small-root theorem suffices to recover the prime from that count in polynomial time, even when the factor sizes differ. The quantitative Boolean tensor-contraction theorem gives a paper bound of $2^{O(n/\sqrt{\log n})}$ time and polynomial space for producing the count. This replaces a sequence of prefix counts with one quarter-width count at the same known asymptotic exponent. Computing it on a general 2048-bit input remains open in practice. [Proof, cost and examples](discoveries/quarter-width-count.md)

For an arbitrary integer $N>1$, one unweighted count of $xy=1+kN$ gives $\varphi(N)$ when $0\le x,y,k<N$. Miller's theorem uses this single value and the Dirichlet hypothesis to recover all prime factors in deterministic polynomial time. One weighted multiplication count gives $\sigma(N)$ instead and allows randomized polynomial-time decoding for arbitrary inputs. [Inverse count and RH connection](discoveries/counting-modular-inverses.md) · [Cost of the weighted contraction](discoveries/tagged-contraction-cost.md)

## One circuit can read every bit of the factor sum

Tag each bit on one input of a multiplication circuit, then count the assignments whose product is $N$. One forward and one reverse pass over the tagged arithmetic circuit give the number of factors with each bit set. Every count fits in the field of three elements. The resulting integer sum determines both factors of **any product of two distinct primes**. Lean checks the readout. The cost of constructing the circuit remains the limiting step. On $595489=641\cdot929$, the example used 157,515 compatible row joins to build a circuit with seven reachable arithmetic gates. [Derivation, upstream factoring proof and limits](discoveries/counting-the-factor-sum.md) · [Reproducible experiments](experiments/bit_marginals.py)

## Two square roots factor a structured 2048-bit input

Suppose $N=pq$ with $p\le q\le2p$ and $(2p+1)(2q+1)$ square. Set $a=\lceil\sqrt N\rceil$ and $h=a(a+1)-N$. Then $h=(p+q)/2$ and the two factors are $h\pm\sqrt{h^2-N}$. The search receives just the product and checks its answer. On a constructed 2048-bit input it recovers two 1024-bit primes with zero Fermat iterations. Lean checks the general formula and both primes in the example. A balanced control misses the formula and remains unresolved at the same budget. [Derivation and limits](discoveries/square-collision-density.md) · [Input and control](benchmarks/shifted.json)

A paper argument using prime distribution proves the formula succeeds on infinitely many balanced inputs whose prime gap is a fixed fraction of the smaller prime. A separate counting argument bounds how many such products occur when a gap of order $X/\log X$ suffices. [Infinitude and density](discoveries/shifted-square-infinitude.md)

## A second 2048-bit example from short modular periods

If the prime predecessors share a large divisor $g=\gcd(p-1,q-1)$, raising a unit to $N-1$ produces coprime periods at the two primes. A search given only $N$, a base and a table budget recovered a different 2048-bit product with 86 entries per table. The bound depends on the smaller residual period. [Proofs, costs and prior work](discoveries/common-predecessors.md) · [Product-only fixtures](benchmarks/reduced-orders.json)

How often does this structure occur? For primes chosen in $[X,2X]$ and fixed $0<\alpha<1$, the proportion with $g\ge X^\alpha$ has order $X^{-\alpha}$. For $\alpha\le1/2$ the paper proof also gives the leading constant $\zeta(2)\zeta(3)/\zeta(6)$. The result is asymptotic. [Counting argument and its hypotheses](discoveries/common-divisor-frequency.md)

A third 2048-bit example uses $N^3-1$. All four $\gcd(p\pm1,q\pm1)$ are at most 12, yet a factor of $p-1$ divides $q^2+q+1$ and leaves a local period of 53. Eight entries in each table suffice. The first two exponent choices exhaust that same budget. The constructed input also has a short weighted Fermat route. [Theorem, counting argument and comparison](discoveries/cyclotomic-periods.md) · [Certified examples and controls](benchmarks/cyclotomic-periods.json)

## Conjectures from the Dirichlet L-function proof

One boundary reading at height 1 determines the **exact integer sum** of two balanced primes if its absolute error is below $1/(8\sqrt N)$. For a 2048-bit product, $2^{-1027}$ suffices. A fast way to obtain that reading remains open. [Precision, derivation and alternatives](discoveries/reading-the-boundary.md)

The quadratic character of the product can also be evaluated directly. An interval of $W$ possible quadratic class numbers gives a factor search using $O(\sqrt W)$ class-group operations per auxiliary prime, plus logarithmic initialization. We derive the auxiliary-prime bound under Dirichlet GRH and check two failures of simpler recovery rules. The analytic truncation estimate still costs about $N^{1/5}$ up to logarithmic factors. [Derivation and Lean proofs](discoveries/quadratic-class-number.md)

For $N=pq$ with $p<q$, Lean proves that the first positive imaginary-axis zero of the principal Dirichlet L-function modulo $N$ has height $2\pi/\log q$. More usefully, a sign computed from one L-value tells whether $q$ lies above an integer threshold $x>\sqrt N$. For balanced primes the library proves an absolute error tolerance at each threshold. Efficiently computing that sign using only $N$ is open. [Derivation and work required](discoveries/character-conjectures.md#comparing-a-factor-with-a-threshold) · [Lean proofs](PrimeFactors/DivisorSignal.lean)

A second investigation bounds how many modular square tests suffice for every discriminant of a given bit length. The universal count grows linearly in the bit length under Dirichlet GRH. The tighter conjecture restricting both the number and size of the primes survived exhaustive examples for widths 9 through 20. We also found small widths where it fails. [Proofs, counterexamples and experiment](discoveries/character-conjectures.md#how-many-primes-suffice-for-all-discriminants)

## What reduces the work?

- **A signed modular exponent covers four relations between the primes.** A public Jacobi symbol chooses an exponent that can exploit a large common divisor of any of $p\pm1$ and $q\pm1$. On 24257, the calculation finds 191 from a successor gcd of 64. Dirichlet GRH bounds how far one must search to encounter each sign pattern. [Lean results, success probabilities and RH connection](discoveries/jacobi-separation.md)
- **A full balanced search can skip most odd trial divisors.** An affine congruence between the high digits gives a deterministic $N^{1/3+o(1)}$ method. On a 61-bit input it reported 20,565 modular candidates across 1,048,576 low classes. A 2048-bit input still requires $2^{683}$ low classes with this construction. [Derivation, cost comparison and limitations](discoveries/modular-hyperbola.md)
- **Higher prime powers have a sharp limit as factor-sum filters.** Every power of one odd prime coprime to the product retains at least one twelfth of the possible sum residues. The limit occurs at powers of three. [Published formula, Lean proof and comparisons](discoveries/prime-power-counts.md)

- **The highest product bits can be replaced by exact tests on the candidate factors.** For a balanced product, one interval on $17x+12y$ replaces the five highest product bits. At 2048 bits, 1,025 public intervals can replace 24 bits. A second construction works for any bounded factors and tests their leading bits directly. In small networks it both saved and added work, depending on the inputs and the number of bits removed. [Proofs, counterexample and measured costs](discoveries/truncated-products.md)

- **Choosing a shift has a provable cost.** At factor width $b$, even a list of $2^{b/2}/b^4$ rational functions of the product misses almost all balanced prime pairs as $b$ grows, under polynomial degree and coefficient-size bounds. This unconditional counting result explains why extending the successful two-square-root formula requires more structure. [Paper bound and Lean components](discoveries/large-sieve-for-shifts.md)
- **Several false midpoints can reveal a factor.** Lean gives sufficient conditions for a square-product triple to split the input and checks a split of 723889. Short triples of this kind are absent for most balanced inputs. [Witness, counterexamples and counting argument](discoveries/multiple-discriminants.md)

- **Weighted collisions improve the table bound to $O(N^{1/5})$.** Two different residues modulo the product can agree modulo one unknown prime. Lean verifies this step of Harvey's method and a matching lower bound on the complete tables used here. On a 2048-bit product, those tables still require more than $2^{408}$ entries. [Derivation and example](discoveries/searching-the-balanced-interval.md#collisions-visible-at-one-unknown-prime)

- **One square test can exclude a whole divisor interval.** On the product 34,387, Lean certifies that one test excludes all fourteen integers from 145 through 158. Changing the weights isolates the divisor 137 in another interval. A theorem for every balanced pair bounds the total number of weighted square tests by $2K(K+1)$ when $K$ is chosen near $N^{1/6}$. [Weighted intervals and the global bound](discoveries/searching-the-balanced-interval.md#one-square-test-for-a-divisor-interval)
- **The sum can be found by matching powers.** Every unit $u$ modulo a product of distinct primes satisfies $u^{p+q}=u^{N+1}$. This lets a classical table search combine two indices and check a window of $W$ sums with roughly $\sqrt W$ entries per table. The note gives the cost of selecting the bases, verifying matches and storing the table. The resulting bound is still exponential in the bit length. [Power tables and their assumptions](discoveries/searching-the-balanced-interval.md#matching-powers-to-recover-the-sum)
- **A stronger modulus can settle a small instance.** For 34,387 the moduli 3, 5 and 7 leave three possible even sums. Replacing 3 with 9 leaves only 388. Lean also identifies exactly which residue classes can benefit from this lift. [Prime-power proofs](PrimeFactors/PrimePower.lean)

## From the product to the sum

Write $S=p+q$. Then $S^2-4N=(q-p)^2$. Once $S$ is known, the roots of $X^2-SX+N$ recover both factors. The unknown is how to obtain enough information about $S$ from $N$ to make finding it cheaper.

For distinct 1,024-bit primes, the balance condition puts $S$ in $[2\sqrt N,3\sqrt{N/2}]$. Our research note deduces from the verified Dirichlet GRH result and a published small-prime theorem that **only the true sum** passes the discriminant test modulo every odd prime below three million in this interval. Lean verifies that such witnesses isolate the sum. The cutoff is derived on paper. The unresolved step is to find that unique integer with less work than checking candidates one at a time. [Isolation argument and sources](discoveries/factor-sum-residues.md#a-uniform-set-of-primes-that-isolates-the-sum) · [Finite Lean theorem](PrimeFactors/Isolation.lean)

- **What one prime tells us.** For any odd prime $\ell$ coprime to $N$, a candidate sum $s$ is compatible with the product modulo $\ell$ exactly when $s^2-4N$ is a square modulo $\ell$, including zero. Precisely $(\ell+1)/2$ residues survive when $N$ is a square modulo $\ell$, and $(\ell-1)/2$ otherwise. Every nonzero residue remains possible for an individual factor. [Local criterion](PrimeFactors/FactorSum.lean) · [Exact count](PrimeFactors/ResidueCount.lean)
- **What several primes tell us.** For coprime moduli the numbers of admissible classes per full period multiply. For example, $N=143$ leaves six possible sum classes modulo 35. It still takes a global constraint to distinguish $11+13$ from locally consistent false sums. [Chinese remainder theorem for sums](PrimeFactors/FactorSumCRT.lean)
- **Where the work remains.** A sparse set over a very long period can still be costly to search in a short interval. The research note bounds how much an exhaustive enumeration of complete periods can save and explains why that bound leaves the short-interval question open. [Derivation, proof status, and literature](discoveries/factor-sum-residues.md)

## Check the mathematics

From a checkout with Elan installed, run the following. Lake reads the pinned compiler and Mathlib versions. The audit checks the axioms used by the project declarations. [Install Lean and Elan](https://lean-lang.org/install/)

```sh
sh scripts/fetch-cache.sh
lake build
lake env lean scripts/Audit.lean
```

## What the Riemann hypothesis contributes

Alpöge’s November 2026 release establishes RH and zero-location results for Dirichlet L-functions. A theorem of Lamzouri, Li and Soundararajan then bounds the first prime outside a proper subgroup. For semiprimes `n = pq ≥ 3000` with `p < q` and `p − 1 ∣ q − 1`, this limits the bases needed to find a gcd split. For distinct primes of the same bit length (at least three bits), the divisibility hypothesis is impossible. The Lean library proves both this limitation and the arithmetic that extracts a factor when the hypothesis holds. The analytic small-witness bound is a published result whose formalization is a research target. The original RH source has no stated redistribution license and is cited by reference. [Release verification](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) · [Independent checks](https://math.mit.edu/~drew/grh/) · [Derivation and upstream licenses](docs/research.md)

A second route gives an exact formula. If `n = pq` for distinct primes and its exact divisor sum `σ(n)` is available, set `s = σ(n) − n − 1`. The factors are `(s ± √(s² − 4n)) / 2`. We prove the integer version in Lean. The Robin bound implied by RH is too wide to narrow the elementary factor interval. Computing `σ(n)` fast enough from `n` alone would be the substantive advance. [Lean theorem](PrimeFactors/DivisorSum.lean) · [Verified Robin consequence](https://math.mit.edu/~drew/grh/ArithSolution.lean)

## Structured examples

| Input family | Result | What made it possible |
| --- | --- | --- |
| Constructed 1,050-bit semiprime | One modular-power witness at base 2 yields a proper divisor. Lean checks both large primes. | The primes satisfy `p − 1 ∣ q − 1`. Their smooth predecessors also make the primality certificates inexpensive. |
| Second constructed 1,050-bit semiprime | No split in 64 tested bases. | One prime is shared with the successful case, but the new pair falls outside the divisibility family. |
| Constructed 100-digit semiprime | Nine Fermat midpoints find both 50-digit primes. | The primes are close enough for their midpoint to fall in a tiny interval above the square root. |
| Same 100-digit input, eight midpoints | Lean excludes every same-parity factor pair with a gap at most 52,915,026,221,291,811,810,032,330. | Failed square tests give a proven exclusion interval. The true pair falls outside it. |

These examples exercise particular theorems and the certificate checker. Each records its assumptions, successful and incomplete runs, and proof files. [Fermat fixtures](benchmarks/cases.json) · [Subgroup fixtures](benchmarks/subgroup.json)

## Reproduce an example

After building the proof library, the example driver requires Python 3.9+.

```sh
python3 scripts/factor.py 10403 --max-steps 1 --verify --lean Factors.lean
```

This produces `[101, 103]`. The generated theorem states `ExactFactorization 10403 [101, 103]`. Replay it with `lake env lean Factors.lean`. You can supply any positive decimal integer, including `1` for the empty factor list. A complete run exits `0`. An unfinished search exits `1` and reports a `remaining` list. An input or checker error exits `2`. `verified` becomes true only after Lean accepts the proof and the axiom audit passes.

To try the 1,050-bit case, read just the input from the fixture. This command supplies neither factor to the search.

```sh
n=$(python3 -c 'import json; print(next(c["n"] for c in json.load(open("benchmarks/subgroup.json")) if c["id"] == "subgroup-1050"))')
python3 scripts/factor.py "$n" --method subgroup --max-base 2 --max-steps 0 --verify --lean Large.lean
```

`--max-steps` counts Fermat midpoints across all splits. `--max-base` sets the inclusive subgroup limit. With no override the subgroup search uses the squared bit length, an integer upper bound for the literature’s `(ln n)²` window. Once a factor is found, small prime stripping and recursive Lucas certificates establish primality where possible. A difficult factor of `p − 1` can leave a cofactor unresolved. `--factor-hint D` lets a separate search program submit a divisor for checking.

## Check the example runs and contribute

```sh
python3 -m unittest discover -s tests
python3 scripts/benchmark.py
python3 scripts/render_site.py
```

The benchmark runner reads expected answers only to compare them with search outputs. It saves each accepted certificate under `build/site/proofs/` and writes `build/site/results.json`. The default-branch workflow publishes that exact output to GitHub Pages after verification. Pull requests run the same checks. [Contributor guide](CONTRIBUTING.md) · [Agent instructions](AGENTS.md) · [Research issue template](.github/ISSUE_TEMPLATE/research.md)
