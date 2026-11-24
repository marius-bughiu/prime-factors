# Prime Factors

What information about two unknown primes can be recovered cheaply from their product alone? This project studies classical integer factorization in Lean 4. A motivating case is a 2,048-bit integer $N=pq$ with two 1,024-bit primes and no supplied relation between them. Progress can be a constructive formula, a proved reduction in the work needed to find a factor, or a proof that a proposed relation leaves too many candidates. [Current research](discoveries/character-conjectures.md) · [Project progress](https://marius-bughiu.github.io/prime-factors/)

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
