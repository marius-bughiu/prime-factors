"""Bound each successful square scale retrospectively on two already factored controls."""

import argparse
import json
from math import gcd, prod
from pathlib import Path

from experiments.certified_control import lean_source
from experiments.offset_winner_positions import published_controls
from scripts.factor import primes_through, render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / 'benchmarks/jacobi-scale-valuations.json'
CHECKED = 'PrimeFactors.Generated.ScaleValuations.checked'
TRIAL_LIMIT = 25_000


def measure(p, q, extra_primes):
    """Inspect the supplied predecessors, using a bounded prime panel and optional certificate primes."""
    predecessors = (p-1)*(q-1)
    rows = []
    for prime in sorted(set(primes_through(TRIAL_LIMIT)).union(extra_primes)):
        remainder = predecessors
        valuation = 0
        while remainder % prime == 0:
            remainder //= prime
            valuation += 1
        if valuation % 2:
            rows.append((prime, valuation))
    shared = gcd(p-1, q-1)
    period = predecessors//(shared*shared)
    forced = prod(prime for prime, _ in rows)
    return dict(period_bits=period.bit_length(), predecessor_gcd=shared, forced_divisor=forced,
                floor_log2=forced.bit_length()-1, valuations=rows)


def proof(n, p, q, result, prime_source, large_proofs):
    forced = result['forced_divisor']
    bits = result['period_bits']
    exponent = result['floor_log2']
    groups = []
    subtotal = 1
    for i, (r, v) in enumerate(result['valuations'], 1):
        prime_proof = large_proofs.get(r, '(by norm_num)')
        groups.extend([
            f'  have divides{i} : {r} ∣ t := odd_valuation_forces (F:=(p-1)*(q-1)) (r:={r}) (k:={(v-1)//2})',
            f'    {prime_proof} decomposition (by decide +kernel) (by decide +kernel)',
            f'  have subtotal{i} : {subtotal}*{r} ∣ t := Nat.Coprime.mul_dvd_of_dvd_of_dvd',
            f'    (by decide +kernel) subtotal{i-1} divides{i}',
        ])
        subtotal *= r
    groups.append(f'  exact subtotal{len(result["valuations"])}')

    return f"""import PrimeFactors.JacobiScaleValuations
{prime_source}
namespace PrimeFactors.Generated.ScaleValuations
open JacobiScaleValuations JacobiPeriodCount JacobiPeriodProbe
set_option exponentiation.threshold 4096

private abbrev p : ℕ := {p}
private abbrev q : ℕ := {q}
private abbrev n : ℕ := p*q
private abbrev R : ℕ := residualProduct p q
private theorem original_product : n={n} := by decide +kernel
local instance : NeZero n := ⟨by decide +kernel⟩

private theorem forced_at {{t : ℕ}} (tp : 0<t) (hit : predecessorSquareSum n t=p+q) :
    {forced} ∣ t := by
  obtain ⟨y,decomposition⟩ := scale_square (p:=p) (q:=q) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) tp hit
  have subtotal0 : 1 ∣ t := one_dvd t
{chr(10).join(groups)}

/-- Uses the previously published prime factors. Every successful positive scale
must be a multiple of the displayed divisor, including the first success. -/
theorem checked : ExactFactorization n [p,q] ∧ (p-1).gcd (q-1)={result['predecessor_gcd']} ∧
    (2^{bits-1} ≤ R ∧ R < 2^{bits}) ∧
    (∀ t, AllOffsets (JacobiMomentPeriod.completeEven n) ((n-1)/2) t ↔ R ∣ t) ∧
    (∀ t, 0<t → predecessorSquareSum n t=p+q → {forced} ∣ t) ∧
    ∀ c z, Squarefree c → R=c*z^2 → 2^{exponent} < c := by
  have fac : ExactFactorization n [p,q] := factorization
  letI : Fact p.Prime := ⟨fac.2 p (by simp)⟩
  letI : Fact q.Prime := ⟨fac.2 q (by simp)⟩
  refine ⟨fac,by decide +kernel,by decide +kernel,?_,fun t => @forced_at t,?_⟩
  · exact fun t => canonical_period (p:=p) (q:=q) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) t
  · intro c z free period
    have hit := (JacobiPeriodSquareClass.first_scale (p:=p) (q:=q) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) free period).1
    exact (show 2^{exponent} < {forced} by decide +kernel).trans_le
      (Nat.le_of_dvd hit.1 (forced_at hit.1 hit.2))

#print axioms checked
end PrimeFactors.Generated.ScaleValuations
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='kernel-check both retrospective receipts')
    args = parser.parse_args()
    expected = {r['id']: r for r in json.loads(FIXTURE.read_text())}
    fresh = json.loads((ROOT/'research/certified-control.json').read_text())
    children = {int(chain[-2]['prime']): f"{side}{chain[-2]['bits']}_prime"
                for side, chain in fresh['chains'].items()}
    for label, n, p, q in published_controls():
        if label == 'small':
            continue
        certificates = children if label == 'fresh' else {}
        result = measure(p, q, certificates)
        # The comparison factors are the diagnostic input. This fixture checks
        # their identity and the outputs after the bounded valuation measurement.
        case = expected[label]
        assert list(map(int, case['factors'])) == [p, q] and p*q == n
        for key in ('predecessor_gcd', 'period_bits', 'forced_divisor', 'floor_log2'):
            assert result[key] == int(case[key]), (label, key)
        print(json.dumps(dict(id=label, trial_prime_limit=TRIAL_LIMIT, **result)), flush=True)
        if args.check:
            prefix = (lean_source(fresh, include_signature=False) if label == 'fresh'
                      else render_certificate(n, [p, q]))
            path = ROOT / f'build/site/proofs/jacobi-scale-valuations-{label}-2048.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(proof(n, p, q, result, prefix, certificates))
            verify_file(path, CHECKED)
            print(f"Lean checked {CHECKED} and its axioms for {label}.", flush=True)


if __name__ == '__main__':
    main()
