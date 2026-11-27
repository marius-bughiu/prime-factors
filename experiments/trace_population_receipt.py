"""Generate and Lean-check all-base population receipts on the certified 2048-bit products."""
import argparse
import json
from pathlib import Path

from experiments.certified_control import lean_source
from experiments.offset_winner_positions import published_controls
from experiments.trace_base_population import parameters
from scripts.factor import render_certificate, verify_file

ROOT = Path(__file__).resolve().parents[1]


FRESH_RATE = """
private theorem order_class (x y : ℕ) (xp : 0<x) (yp : 0<y) (xd : x∣p-1) (yd : y∣q-1) :
    Wins setup qs x y ↔ (x=7 ∨ x=14) ∧ y=8 := by
  rw [order_table coverage xp yp xd yd, listed]
  simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
  tauto

private def examplePower := ((p-1)/7).lcm ((q-1)/8)
private def Calibration :=
  (p-1)/(p-1).gcd examplePower=7 ∧ (q-1)/(q-1).gcd examplePower=8 ∧
  112*examplePower=(p-1)*(q-1) ∧
  7*PoweredTraceLimit.count ((p-1)/(p-1).gcd examplePower)
    ((q-1)/(q-1).gcd examplePower)=3*(((p-1)/(p-1).gcd examplePower)*
    ((q-1)/(q-1).gcd examplePower))

private theorem calibration : Calibration := by unfold Calibration; decide +kernel

private def Recovery := ∀ E : ℕ, 0<E → E≤n →
  (p-1)*(q-1) ≤ (Finset.univ.filter (fun z : (ZMod p)ˣ × (ZMod q)ˣ =>
    Wins setup qs (orderOf (z.1^E)) (orderOf (z.2^E)))).card*2^503 →
  ∃ i, (E : ℚ)/((p-1)*(q-1) : ℕ) = ((E : ℝ)/n).convergent i

private theorem recovery : Recovery := by
  intro E _ en raw
  have pd (z : (ZMod p)ˣ) : orderOf z∣p-1 :=
    (Nat.prime_iff_card_units p).mp (Fact.out) ▸ orderOf_dvd_card
  have qd (z : (ZMod q)ˣ) : orderOf z∣q-1 :=
    (Nat.prime_iff_card_units q).mp (Fact.out) ▸ orderOf_dvd_card
  have loc (z : (ZMod p)ˣ × (ZMod q)ˣ) :
      Wins setup qs (orderOf (z.1^E)) (orderOf (z.2^E)) ↔
        (orderOf (z.1^E)=7 ∨ orderOf (z.1^E)=14) ∧ orderOf (z.2^E)=8 :=
    order_class _ _ (orderOf_pos _) (orderOf_pos _) (pd _) (qd _)
  simp_rw [loc] at raw
  exact PowerImageDenominator.rate_convergent (p:=p) (q:=q)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) en raw
"""


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
    return "import PrimeFactors.TraceOrderPopulation\nimport PrimeFactors.PowerImageDenominator\n" + primes + f"""
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

private theorem coverage : coverTable (p-1) (q-1) {bounds[0]} {bounds[1]} setup qs=true := by decide +kernel
private theorem listed : orders (p-1) (q-1) {bounds[0]} {bounds[1]} setup qs={order_set} := by decide +kernel

theorem all_bases : (winningBases cop setup qs).card = {expected} :=
  certified_count cop {bounds[0]} {bounds[1]} setup qs {order_set} {expected}
    coverage listed (by decide +kernel)

theorem off_bases : (winningBases cop setup offQs).card = 0 :=
  certified_count cop 0 0 setup offQs ∅ 0 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

{FRESH_RATE if label=="fresh" else ""}
theorem counts : (winningBases cop setup qs).card = {expected} ∧
    (winningBases cop setup offQs).card = 0{" ∧ Recovery ∧ Calibration" if label=="fresh" else ""} :=
  ⟨all_bases,off_bases{",recovery,calibration" if label=="fresh" else ""}⟩

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
