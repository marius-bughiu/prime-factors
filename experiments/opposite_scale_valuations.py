"""Retrospectively exclude four signed square scales through 2^40 on two published factored controls."""

import argparse
import json
from math import prod
from pathlib import Path

from experiments.certified_control import lean_source
from experiments.offset_winner_positions import published_controls
from scripts.factor import primes_through, render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = ROOT / 'benchmarks/opposite-scale-valuations.json'
CHECKED = 'PrimeFactors.Generated.OppositeScaleValuations.checked'
TRIAL_LIMIT = 25_000
CAP = 2**40
# The subscripts are the signs applied to the supplied smaller and larger primes.
SIGNS = (
    ('minusMinus', -1, -1), ('minusPlus', -1, 1),
    ('plusMinus', 1, -1), ('plusPlus', 1, 1),
)


def square_mask(prime):
    """Set bit r when r is a square modulo the supplied prime, including zero."""
    return sum(1 << r for r in {a*a % prime for a in range(prime)})


def measure_branch(product, primes):
    """Every t with product=t*z² is forced*k, so k*(product/forced)=(k*z)²."""
    valuations = []
    for prime in primes:
        remaining = product
        v = 0
        while remaining % prime == 0:
            remaining //= prime
            v += 1
        if v % 2:
            valuations.append([prime, v])
    forced = prod(prime for prime, _ in valuations)
    reduced = product // forced
    limit = CAP // forced
    # These two disclosed full-size controls use at most 4,197 trial multipliers.
    if limit > 5_000:
        raise ValueError('outside the bounded retrospective fixture')
    candidates = list(range(1, limit+1))
    screens = []
    for prime in primes_through(97):
        residue = reduced % prime
        mask = square_mask(prime)
        keep = [k for k in candidates if mask >> (k*residue % prime) & 1]
        # Each row records the modulus, reduced product residue and surviving count.
        if len(keep) < len(candidates):
            screens.append([prime, residue, len(keep)])
        candidates = keep
        if not candidates:
            break
    return dict(valuations=valuations, forced_divisor=forced, max_multiplier=limit,
                screens=screens, remaining_multipliers=candidates)


def measure(p, q, extra_primes):
    base = set(primes_through(TRIAL_LIMIT))
    return {name: measure_branch((p+a)*(q+b), sorted(base.union(extra_primes)))
            for name, a, b in SIGNS}


def branch_proof(name, a, b, p, q, result, large_proofs):
    forced = result['forced_divisor']
    limit = result['max_multiplier']
    reduced = (p+a)*(q+b) // forced
    expression = f'(p{a:+d})*(q{b:+d})'
    if result['remaining_multipliers']:
        raise ValueError('modular screens did not prove complete coverage')

    valuation_lines = ['  have subtotal0 : 1 ∣ t := one_dvd t']
    subtotal = 1
    for i, (r, v) in enumerate(result['valuations'], 1):
        valuation_lines.extend([
            f'  have divides{i} : {r} ∣ t := JacobiScaleValuations.odd_valuation_forces',
            f"    (F:=F) (r:={r}) (k:={(v-1)//2}) {large_proofs.get(r, '(by norm_num)')}",
            '    rep (by decide +kernel) (by decide +kernel)',
            f'  have subtotal{i} : {subtotal}*{r} ∣ t := Nat.Coprime.mul_dvd_of_dvd_of_dvd',
            f'    (by decide +kernel) subtotal{i-1} divides{i}',
        ])
        subtotal *= r
    valuation_lines.append(f'  exact subtotal{len(result["valuations"])}')

    beginning = f"""
namespace {name}
private abbrev F : ℕ := {expression}
private abbrev D : ℕ := {forced}
private theorem forced_at {{t z : ℕ}} (rep : t*z^2=F) : D ∣ t := by
{chr(10).join(valuation_lines)}
"""
    if not limit:
        return beginning + f"""
private theorem excluded {{t z : ℕ}} (tp : 0<t) (cap : t≤2^40) : t*z^2≠F := by
  intro rep
  exact (not_le_of_gt (by decide +kernel : 2^40<D)) ((Nat.le_of_dvd tp (forced_at rep)).trans cap)
end {name}
"""

    tests = []
    local_checks = []
    hypotheses = []
    for prime, residue, _ in result['screens']:
        mask = square_mask(prime)
        test = f'Nat.testBit {mask} ((k*{residue})%{prime})'
        tests.append(test)
        hypotheses.append(f'h{prime}')
        local_checks.extend([
            f'  have h{prime} : {test}=true := square_pass',
            f'    (B:=B) (z:=z) (k:=k) (l:={prime}) (b:={residue}) (mask:={mask})',
            '    (by decide) (by decide +kernel) rep (by decide +kernel)',
        ])
    local_checks.append('  simp only [allowed,' + ','.join(hypotheses) + ']')
    local_checks.append('  decide')
    # Tile the individually checked entries to avoid a long recursion on Fin 4197.
    width = 64
    blocks = (limit + width - 1)//width

    return beginning + f"""
private abbrev B : ℕ := {reduced}

private def allowed (k : ℕ) : Bool :=
  {' && '.join(tests)}

private theorem would_pass {{k z : ℕ}} (rep : B=k*z^2) : allowed k=true := by
{chr(10).join(local_checks)}

private theorem veto (k : ℕ) (kp : 0<k) (hi : k≤{limit}) : allowed k=false := by
  let b : Fin {blocks} := ⟨(k-1)/{width},by omega⟩
  let i : Fin {width} := ⟨(k-1)%{width},Nat.mod_lt _ (by decide)⟩
  have grid : ∀ b : Fin {blocks}, ∀ i : Fin {width},
      {width}*b.val+i.val+1≤{limit} → allowed ({width}*b.val+i.val+1)=false := by decide +kernel
  have point : {width}*b.val+i.val+1=k := by dsimp [b,i]; omega
  rw [←point]
  exact grid b i (by rwa [point])

private theorem excluded {{t z : ℕ}} (tp : 0<t) (cap : t≤2^40) : t*z^2≠F := by
  intro rep
  obtain ⟨k,hk⟩ := forced_at rep
  have reduced : B=k*z^2 := Nat.eq_of_mul_eq_mul_left (show 0<D by decide) (by
    calc D*B = F := by decide +kernel
         _ = t*z^2 := rep.symm
         _ = D*(k*z^2) := by rw [hk,Nat.mul_assoc])
  have kp : 0<k := by
    by_contra! zero
    have k0 : k=0 := by omega
    simp [k0] at hk
    omega
  have hi : k≤(2^40)/D := (Nat.le_div_iff_mul_le (by decide : 0<D)).mpr
    (calc k*D = t := (Nat.mul_comm ..).trans hk.symm
          _ ≤ 2^40 := cap)
  have bound : (2^40)/D={limit} := by decide +kernel
  rw [bound] at hi
  exact Bool.noConfusion ((veto k kp hi).symm.trans (would_pass reduced))

end {name}
"""


def proof(n, p, q, results, prime_source, large_proofs):
    branches = [branch_proof(name, a, b, p, q, results[name], large_proofs) for name, a, b in SIGNS]
    return f"""import PrimeFactors.SuccessorSquareScale
import PrimeFactors.JacobiScaleValuations
{prime_source}
namespace PrimeFactors.Generated.OppositeScaleValuations

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private abbrev p : ℕ := {p}
private abbrev q : ℕ := {q}
private abbrev n : ℕ := p*q
private theorem original_product : n={n} := by decide +kernel

private theorem square_pass {{B z k l b mask : ℕ}} (lp : 0<l) (res : B%l=b)
    (rep : B=k*z^2)
    (table : ∀ a : Fin l, mask.testBit ((a.val*a.val)%l)=true) :
    mask.testBit ((k*b)%l)=true := by
  let a : Fin l := ⟨(k*z)%l,Nat.mod_lt _ lp⟩
  have sq : k*B=(k*z)*(k*z) := by rw [rep]; ring
  have e : (k*b)%l=(a.val*a.val)%l := calc
    _ = (k*B)%l := by rw [←res,Nat.mul_mod_mod]
    _ = ((k*z)*(k*z))%l := by rw [sq]
    _ = _ := Nat.mul_mod _ _ _
  rw [e]
  exact table a

{chr(10).join(branches)}

private theorem successor_excluded {{t : ℕ}} (tp : 0<t) (cap : t≤2^40) :
    SuccessorSquareScale.sum n t≠p+q := by
  intro hit
  obtain ⟨z,rep⟩ := (SuccessorSquareScale.sum_iff (p:=p) (q:=q) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) tp).mp hit
  exact plusPlus.excluded tp cap rep

/-- On this disclosed pair each of the four products has squarefree part above 2^40. -/
theorem checked : ExactFactorization n [p,q] ∧
    (∀ t z : ℕ, 0<t → t≤2^40 →
      t*z^2≠(p-1)*(q-1) ∧ t*z^2≠(p-1)*(q+1) ∧ t*z^2≠(p+1)*(q-1) ∧ t*z^2≠(p+1)*(q+1)) ∧
    (∀ t, 0<t → SuccessorSquareScale.sum n t=p+q → {results['plusPlus']['forced_divisor']} ∣ t) ∧
    (∀ t, 0<t → t≤2^40 → SuccessorSquareScale.sum n t≠p+q) ∧
    ∀ c U, Squarefree c → (p+1)*(q+1)=c*U^2 → 2^40<c := by
  refine ⟨factorization,?_,?_,fun t => @successor_excluded t,?_⟩
  · intro t z tp cap
    exact ⟨minusMinus.excluded tp cap,minusPlus.excluded tp cap,
      plusMinus.excluded tp cap,plusPlus.excluded tp cap⟩
  · intro t tp hit
    obtain ⟨z,rep⟩ := (SuccessorSquareScale.sum_iff (p:=p) (q:=q) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) tp).mp hit
    exact plusPlus.forced_at rep
  · intro c U free rep
    have first := (SuccessorSquareScale.first_scale (p:=p) (q:=q) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) free rep).1
    exact lt_of_not_ge (fun small => successor_excluded first.1 small first.2)

#print axioms checked
end PrimeFactors.Generated.OppositeScaleValuations
"""


def construction_primes(fresh):
    return {int(chain[-2]['prime']): f"{side}{chain[-2]['bits']}_prime"
            for side, chain in fresh['chains'].items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='kernel-check both exclusions')
    args = parser.parse_args()
    fixture = json.loads(FIXTURE.read_text())
    assert fixture['cap'] == CAP and fixture['trial_prime_limit'] == TRIAL_LIMIT
    cases = {row['id']: row for row in fixture['cases']}
    fresh = json.loads((ROOT/'research/certified-control.json').read_text())
    for label, n, p, q in published_controls():
        if label == 'small':
            continue
        large_proofs = construction_primes(fresh) if label == 'fresh' else {}
        results = measure(p, q, large_proofs)
        # The disclosed pair is diagnostic input. The independent fixture only checks output.
        assert n == p*q and cases[label] == dict(id=label, factors=[str(p), str(q)], branches=results)
        assert all(not branch['remaining_multipliers'] for branch in results.values())
        print(json.dumps(dict(id=label, branches=results)), flush=True)
        if args.check:
            if label == 'fresh':
                prefix = lean_source(fresh, include_signature=False)
            else:
                prefix = render_certificate(n, [p, q])
            path = ROOT / f'build/site/proofs/opposite-scale-valuations-{label}-2048.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(proof(n, p, q, results, prefix, large_proofs))
            verify_file(path, CHECKED)
            print(f'Lean checked {CHECKED} and its axioms for {label}.', flush=True)


if __name__ == '__main__':
    main()
