"""Generate and kernel-check a Bézout receipt for a consecutive block of integers."""
from time import perf_counter

from experiments.block_exclusion_certificate import generate, verify
from experiments.short_pascal_row import interval
from scripts.factor import verify_file


def _exclusion_source(n, start, lower, upper, side, count, u, v):
    # The equal-width receipt checks that the first integer comes from N's
    # bit length and that the complete block fits below sqrt(N).
    if start == 'equal-width':
        exponent = n.bit_length() - 1
        origin = 'ShortPascalRow.lower modulus (2 ^ (Nat.log2 modulus / 2))'
        geometry = f"""have bits : Nat.log2 modulus = {exponent} := Nat.eq_of_le_of_lt_succ
      ((Nat.le_log2 (by decide : modulus ≠ 0)).mpr (by decide +kernel))
      ((Nat.log2_lt (by decide : modulus ≠ 0)).mpr (by decide +kernel))
    unfold first
    rw [bits]
    decide +kernel"""
        bound = f' ∧ {upper}^2 ≤ modulus'
    else:
        origin = str(lower)
        geometry = 'decide +kernel'
        bound = ''
    return f"""import PrimeFactors.BlockExclusionCheck
import PrimeFactors.ShortPascalRow

namespace PrimeFactors.Generated
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def modulus : ℕ := {n}
def first : ℕ := {origin}
private def u : List ℕ := {u}
private def v : List ℕ := {v}

/-- The endpoints and the Bézout identity are checked independently. -/
theorem blockExclusion : (first = {lower}{bound}) ∧
    ∀ x : ℕ, {lower} ≤ x → x ≤ {upper} → x.Coprime modulus := by
  constructor
  · {geometry}
  · intro x lo hi
    apply BlockExclusionCheck.interval (base := {lower}) (side := {side}) (count := {count})
      (u := u) (v := v) (by decide) (by decide +kernel) lo
    exact Nat.lt_of_le_of_lt hi (by decide +kernel)

#print axioms blockExclusion
end PrimeFactors.Generated
"""


def block_exclusion_case(case, proof, agree, certify_split):
    n, start = int(case['n']), case['start']
    side, count = case['side'], case['count']
    if side < 1 or count < 1:
        raise ValueError('block dimensions must be positive')
    began = perf_counter()
    if start == 'equal-width':
        lower, feasible_upper = interval(n)
        if lower + side * count - 1 > feasible_upper:
            raise ValueError('block extends beyond the equal-width interval')
    else:
        lower = int(start)
    upper = lower + side * count - 1
    offsets = list(range(side))
    nodes = [lower + side * j for j in range(count)]
    outcome = generate(n, offsets, nodes)
    elapsed = perf_counter() - began

    u, v = outcome['u'], outcome['v']
    report = dict(outcome=outcome['status'], start=start, lower=str(lower), upper=str(upper),
                  side=side, count=count, positions=side * count, work=outcome['work'],
                  collision=outcome['collision'], witness_coefficients=len(u or []) + len(v or []))
    agree({'id': case['id'], **case['checks']}, report, case['checks'])
    result = certify_split(case, proof, outcome['factor'], elapsed, 'block_exclusion', report)
    if outcome['status'] == 'certified':
        if not verify(n, offsets, nodes, u, v):
            raise ValueError(f"invalid Bézout coefficients on {case['id']}")
        proof.write_text(_exclusion_source(n, start, lower, upper, side, count, u, v))
        began = perf_counter()
        verify_file(proof, 'PrimeFactors.Generated.blockExclusion')
        result['exclusion'] = dict(lower=str(lower), upper=str(upper), proof=f'proofs/{proof.name}',
                                   verification_seconds=perf_counter()-began)
    return result
