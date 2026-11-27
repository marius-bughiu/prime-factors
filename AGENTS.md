# Working on prime-factors

## Responsible disclosure

If you find a plausible major factoring breakthrough, keep the result private and ask the user for human review in the private working conversation. A practical way to factor arbitrary balanced 2,048-bit semiprimes, or a general reduction that could materially weaken deployed cryptography, qualifies even while verification is incomplete.

Hold public pushes, including to branches and forks, and keep the finding out of issues, pull requests, CI logs and artifacts, and GitHub Pages. This includes partial proofs, code, examples, and benchmarks that could reveal the method. The review requirement takes precedence over routine instructions to push progress to `main`. Resume publication of the affected material only after the human reviewers coordinate responsible disclosure and explicitly approve what may be released and when. [Contributor guidance](CONTRIBUTING.md#responsible-disclosure)

## Research workflow

Start with `README.md` for the research question and `discoveries/searching-the-balanced-interval.md` for the current mathematical results. `docs/research.md` records the assumptions behind the RH connections. For a new theoretical route, state what is known about the input, how the relation constrains its unknown factors, and what work is required to use the constraint. The directory `PrimeFactors/` contains the proof library. Import each public module from `PrimeFactors.lean`. The Python search can propose witnesses. Lean checks the product and primality of every claimed prime factor, including its multiplicity.

Run `lake build`, `lake env lean scripts/Audit.lean`, and `python3 -m unittest discover -s tests` after relevant changes. For changes to discovery, proof generation, or benchmarks, also run `python3 scripts/benchmark.py` against the pinned toolchain. A complete result has a checked certificate. Keep unresolved cofactors and spent budgets visible in partial results.

For incremental checks, pass `--cache-dir build/verification-cache` to the benchmark runner and to `python3 scripts/verify_checks.py`. Use a cache created by your own checks or the trusted main workflow. Keep each row’s original measurement and verification provenance when rebuilding the report. [Incremental and full replay](CONTRIBUTING.md#verification)

Use bounded, reproducible examples in CI. Add a benchmark fixture with expected factors stored as decimal strings. The benchmark runner may use expected factors only to check output. Cite the origin and license of code you reuse. In the pull request, explain AI assistance, the mathematics you verified, and the checks you ran.

For every commit Codex helps write, add the Git trailer `Co-authored-by: Codex <noreply@openai.com>`. Use `git commit --trailer 'Co-authored-by: Codex <noreply@openai.com>'` when committing from the command line.

## Public research findings

Add reviewed public results to `site/findings.json` with a distinct title, an impact category, a concrete outcome, its scope, and sources. State when an example used specially chosen primes or a supplied clue. The Pages report displays every finding in one row with the All filter selected by default.
