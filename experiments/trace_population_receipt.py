"""Generate and Lean-check all-base population receipts on the certified 2048-bit products."""
import argparse
import json
from pathlib import Path

from experiments.certified_control import lean_source
from experiments.offset_winner_positions import published_controls
from experiments.trace_base_population import parameters
from scripts.factor import render_certificate, verify_file

ROOT = Path(__file__).resolve().parents[1]


def source(label, n, p, q):
    gaps, queries, _, off, _ = parameters(n, 1024, 64, 2)
    if label == "fresh":
        record = json.loads((ROOT/"research/certified-control.json").read_text())
        primes = lean_source(record, include_signature=False)
        bounds = (14, 8)
        order_set = "{(7,8),(14,8)}"
        expected = 48
    elif label == "crossed":
        primes = render_certificate(n, [p, q])
        bounds = (0, 0)
        order_set = "∅"
        expected = 0
    else:
        raise ValueError("expected fresh or crossed")
    rows = ",\n    ".join(f"({c},{s},{d})" for c, s, d in queries)
    off_indices = [i for i, row in enumerate(queries) if row in off]
    return "import PrimeFactors.TraceOrderPopulation\n" + primes + f"""
namespace PrimeFactors.Generated.TracePopulation
open TraceOrderPopulation

private abbrev p : ℕ := {p}
private abbrev q : ℕ := {q}
private abbrev n : ℕ := {n}

private theorem primes : ExactFactorization n [p,q] := factorization
private instance : Fact p.Prime := ⟨primes.2 p (by simp)⟩
private instance : Fact q.Prime := ⟨primes.2 q (by simp)⟩
private theorem cop : p.Coprime q := Nat.coprime_primes (Fact.out) (Fact.out) |>.mpr (by decide +kernel)

private def setup : List ℕ := ({gaps} : List ℕ).map ((n-1)*·)
private def coords : List (ℕ × ℕ × ℕ) :=
  [{rows}]
private def qs := coords.map fun z => query (n/2) z.1 z.2.1 z.2.2
private def offQs := ({off_indices} : List ℕ).map fun i => qs[i]!

set_option maxHeartbeats 0

theorem all_bases : (winningBases cop setup qs).card = {expected} :=
  certified_count cop {bounds[0]} {bounds[1]} setup qs {order_set} {expected}
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem off_bases : (winningBases cop setup offQs).card = 0 :=
  certified_count cop 0 0 setup offQs ∅ 0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem counts : (winningBases cop setup qs).card = {expected} ∧
    (winningBases cop setup offQs).card = 0 := ⟨all_bases,off_bases⟩

#print axioms counts
end PrimeFactors.Generated.TracePopulation
"""


def check(label, n, p, q):
    path = ROOT / "build/site/proofs" / f"trace-population-{label}-2048.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source(label, n, p, q))
    verify_file(path, "PrimeFactors.Generated.TracePopulation.counts")


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("labels", nargs="*", help="fresh and/or crossed (defaults to both)")
    args = cli.parse_args()
    selected = args.labels or ["fresh", "crossed"]
    if set(selected) - {"fresh", "crossed"}:
        cli.error("expected fresh or crossed")
    for control in published_controls():
        if control[0] in selected:
            check(*control)
            print(f"{control[0]} factorization and population counts verified", flush=True)
