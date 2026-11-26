"""Replay the empty-sum lane product and certify its split or ordinary terminal sum exclusion."""

from time import perf_counter

from experiments.reciprocal_sum_lanes import band, search
from scripts.factor import render_certificate, verify_file


TERMINAL = """
namespace PrimeFactors.Generated
private theorem sumExcludes {n l t p q : ℕ} (square : t*t<n)
    (upper : n+l*l<l*(2*t+1)) (left : l≤p) (ordered : p≤q) : p*q≠n := by
  rintro rfl
  have lower : 2*t+1≤p+q := by
    by_contra! small
    have sq := Nat.mul_self_le_mul_self (show p+q≤2*t by omega)
    zify at sq square
    nlinarith only [sq,square,sq_nonneg ((q:ℤ)-(p:ℤ))]
  have product := Nat.mul_le_mul_left l lower
  zify at product upper left ordered
  nlinarith only [product,upper,mul_nonneg (sub_nonneg.mpr left) (sub_nonneg.mpr (left.trans ordered))]

private theorem terminal {n l t : ℕ} (square : t*t<n) (upper : n+l*l<l*(2*t+1)) :
    ∀ p : ℕ, l≤p → p≤t → ¬p∣n := by
  rintro p left right ⟨q,eq⟩
  have ordered : p≤q := by
    by_contra! small
    have cap := Nat.mul_self_le_mul_self right
    have lim := Nat.mul_le_mul_left p small.le
    omega
  exact sumExcludes square upper left ordered eq.symm
"""


def terminal_receipt(n, start, top, band_low, width, count):
    total = (top-band_low)//width+1
    return f"""import PrimeFactors.ReciprocalSumLanes
{TERMINAL}
private def modulus : ℕ := {n}
private def bottom : ℕ := {band_low}
private def first : ℕ := {start}
private def top : ℕ := {top}
set_option maxRecDepth 8192

/-- Integer comparisons also reconstruct the first and last band endpoints
and the first position in the final {count} blocks. -/
theorem terminalExclusion :
    (2*(bottom-1)^2<modulus ∧ modulus≤2*bottom^2 ∧
     top*top<modulus ∧ modulus<(top+1)^2 ∧
     (top-bottom)/{width}+1={total} ∧ first=bottom+({total}-{count})*{width}) ∧
    ∀ p : ℕ, first≤p → p≤top → ¬p∣modulus := by
  constructor
  · decide +kernel
  · exact terminal (by decide +kernel) (by decide +kernel)

#print axioms terminalExclusion
end PrimeFactors.Generated
"""


def split_receipt(n, factor, residue):
    other = n//factor
    return render_certificate(n, [factor, other]) + f"""
namespace PrimeFactors.Generated
/-- The reported modular product gives this proper gcd, and both factors are prime. -/
theorem laneSplit : Nat.gcd {residue} {n}={factor} ∧
    ExactFactorization {n} {sorted([factor, other])} :=
  ⟨by decide +kernel, factorization⟩
#print axioms laneSplit
end PrimeFactors.Generated
"""


def reciprocal_sum_lane_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    run = search(n, case['wheel'], case['width'], case['max_blocks'],
                 from_end=case['from_end'], method=case['policy'])
    elapsed = perf_counter()-start
    factor = run.pop('factor')
    run.update(wheel=case['wheel'], width=case['width'], budget=case['max_blocks'],
               from_end=case['from_end'], policy=case['policy'])
    agree(dict(id=case['id'], **case['checks']), run, case['checks'])
    result = certify_split(case, proof, None, elapsed, 'reciprocal_sum_lanes', run)
    if factor is not None:
        start = perf_counter()
        proof.write_text(split_receipt(n, factor, run['product']))
        check = perf_counter()
        verify_file(proof, 'PrimeFactors.Generated.laneSplit')
        result.update(factors=list(map(str, sorted((factor, n//factor)))), remaining=[], status='complete',
                      verified=True, verification_seconds=perf_counter()-check, certificate_seconds=perf_counter()-start)
    elif case.get('ordinary_terminal_exclusion'):
        low, high = band(n)
        left = low+int(run['first_block'])*case['width']
        if not case['from_end'] or not run['work']['blocks'] or not (high*high<n and n+left*left<left*(2*high+1)):
            raise ValueError('terminal sum interval did not exclude the requested window')
        proof.write_text(terminal_receipt(n, left, high, low, case['width'], run['work']['blocks']))
        check = perf_counter()
        verify_file(proof, 'PrimeFactors.Generated.terminalExclusion')
        result['exclusion'] = dict(lower=str(left), upper=str(high), proof=f'proofs/{proof.name}',
                                   verification_seconds=perf_counter()-check, method='ordinary integer sum')
    return result
