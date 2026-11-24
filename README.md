# Prime Factors

What information about two unknown primes can be recovered cheaply from their product alone? This project studies classical integer factorization in Lean 4. A motivating case is a 2,048-bit integer $N=pq$ with two 1,024-bit primes and no supplied relation between them. Progress can be a constructive formula, a proved reduction in the work needed to find a factor, or a proof that a proposed relation leaves too many candidates. [Current research](discoveries/factor-sum-residues.md) · [Project progress](https://marius-bughiu.github.io/prime-factors/)

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
