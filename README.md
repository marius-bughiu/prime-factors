# Prime Factors

A Lean 4 research project for finding the prime factors of large integers and proving which parts of a search can be skipped. Python finds candidate factors. Lean checks their primality, multiplicities and product against the original integer. An exact result can be replayed from a single generated `.lean` file. [Live benchmarks and proof downloads](https://marius-bughiu.github.io/prime-factors/) · [Verification runs](https://github.com/marius-bughiu/prime-factors/actions/workflows/verify.yml)

## Results to reproduce

| Input family | Result | What made it possible |
| --- | --- | --- |
| Constructed 1,050-bit semiprime | One modular-power witness at base 2 yields a proper divisor. Lean checks both large primes. | The primes satisfy `p − 1 ∣ q − 1`. Their smooth predecessors also make the primality certificates inexpensive. |
| Second constructed 1,050-bit semiprime | No split in 64 tested bases. | One prime is shared with the successful case, but the new pair falls outside the divisibility family. |
| Constructed 100-digit semiprime | Nine Fermat midpoints find both 50-digit primes. | The primes are close enough for their midpoint to fall in a tiny interval above the square root. |
| Same 100-digit input, eight midpoints | Lean excludes every same-parity factor pair with a gap at most 52,915,026,221,291,811,810,032,330. | Failed square tests give a proven exclusion interval. The true pair falls outside it. |

The research target is one hour from a decimal input to its checked prime list on a modern PC. These benchmarks measure structured inputs. An hour bound for arbitrary large integers remains open here. The progress page includes incomplete runs, hardware, wall times and source revisions. [Fermat fixtures](benchmarks/cases.json) · [Subgroup fixtures](benchmarks/subgroup.json)

## Run it

Use Python 3.9+ and Elan. Lake selects Lean 4.19.0 from `lean-toolchain` and fetches the Mathlib revision in the manifest. From the repository root, run the following. [Install Lean and Elan](https://lean-lang.org/install/)

```sh
sh scripts/fetch-cache.sh
lake build
python3 scripts/factor.py 10403 --max-steps 1 --verify --lean Factors.lean
```

This produces `[101, 103]`. The generated theorem states `ExactFactorization 10403 [101, 103]`. Replay it with `lake env lean Factors.lean`. You can supply any positive decimal integer, including `1` for the empty factor list. A complete run exits `0`. An unfinished search exits `1` and reports a `remaining` list. An input or checker error exits `2`. `verified` becomes true only after Lean accepts the proof and the axiom audit passes.

To try the 1,050-bit case, read just the input from the fixture. This command supplies neither factor to the search.

```sh
n=$(python3 -c 'import json; print(next(c["n"] for c in json.load(open("benchmarks/subgroup.json")) if c["id"] == "subgroup-1050"))')
python3 scripts/factor.py "$n" --method subgroup --max-base 2 --max-steps 0 --verify --lean Large.lean
```

`--max-steps` counts Fermat midpoints across all splits. `--max-base` sets the inclusive subgroup limit. With no override the subgroup search uses the squared bit length, an integer upper bound for the literature’s `(ln n)²` window. Once a factor is found, small prime stripping and recursive Lucas certificates establish primality where possible. A difficult factor of `p − 1` can leave a cofactor unresolved. `--factor-hint D` lets a separate search program submit a divisor for checking.

## What the Riemann hypothesis contributes

Alpöge’s November 2026 release establishes RH and zero-location results for Dirichlet L-functions. A theorem of Lamzouri, Li and Soundararajan then bounds the first prime outside a proper subgroup. For semiprimes `n = pq ≥ 3000` with `p < q` and `p − 1 ∣ q − 1`, this limits the bases needed to find a gcd split. The arithmetic that extracts the factor from a witness is formalized here. The analytic small-witness bound is a published result whose formalization is a research target. The original RH source has no stated redistribution license and is cited by reference. [Release verification](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) · [Independent checks](https://math.mit.edu/~drew/grh/) · [Derivation and upstream licenses](docs/research.md)

A second route gives an exact formula. If `n = pq` for distinct primes and its exact divisor sum `σ(n)` is available, set `s = σ(n) − n − 1`. The factors are `(s ± √(s² − 4n)) / 2`. We prove the integer version in Lean. The Robin bound implied by RH is too wide to narrow the elementary factor interval. Computing `σ(n)` fast enough from `n` alone would be the substantive advance. [Lean theorem](PrimeFactors/DivisorSum.lean) · [Verified Robin consequence](https://math.mit.edu/~drew/grh/ArithSolution.lean)

## Verify and contribute

```sh
lake env lean scripts/Audit.lean
python3 -m unittest discover -s tests
python3 scripts/benchmark.py
python3 scripts/render_site.py
```

The benchmark runner reads expected answers only to compare them with search outputs. It saves each accepted certificate under `build/site/proofs/` and writes `build/site/results.json`. The default-branch workflow publishes that exact output to GitHub Pages after verification. Pull requests run the same checks. [Contributor guide](CONTRIBUTING.md) · [Agent instructions](AGENTS.md) · [Research issue template](.github/ISSUE_TEMPLATE/research.md)
