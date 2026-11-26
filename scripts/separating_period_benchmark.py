"""Check a separating period and its minimality on every published input."""
from time import perf_counter

from experiments.separating_period import search
from scripts.factor import verify_file


def period_case(case, proof, agree, certify_split):
    start = perf_counter()
    wheel, limit = case['wheel'], case['period_limit']
    reflect = case['reflect']
    work = search(int(case['n']), wheel=wheel, period_limit=limit, reflect=reflect,
                  max_work=case['max_work'])
    elapsed = perf_counter()-start
    factor = work.pop('factor')
    work['found_divisor'] = None if factor is None else str(factor)
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    result = certify_split(case, proof, factor, elapsed, 'separating_period', work)
    period = work['period']
    if period is None:
        return result

    receipt = proof.with_name(f'{proof.stem}-period.lean') if result['verified'] else proof
    mirror = str(reflect).lower()
    evaluates = (f" ∧ Nat.gcd {work['product']} n = {factor}"
                 if work['outcome'] == 'column_gcd' else '')
    receipt.write_text(f"""import PrimeFactors.SymmetricDivisorSelector

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace PrimeFactors.Generated
open SymmetricDivisorSelector

private abbrev n : ℕ := {case['n']}

/-- The chosen wheel multiple works and all earlier coprime multiples fail.
The equivalence with an actual separator is SymmetricDivisorSelector.works_iff. -/
theorem periodMinimal :
    Nat.Coprime n {period} ∧ {wheel} * {period//wheel} = {period} ∧
    works n {period} {mirror} = true ∧
    (∀ j : Fin {period//wheel-1}, n.Coprime ({wheel}*(j.val+1)) →
      works n ({wheel}*(j.val+1)) {mirror} = false){evaluates} := by
  decide +kernel

#print axioms periodMinimal
end PrimeFactors.Generated
""")
    start = perf_counter()
    verify_file(receipt, 'PrimeFactors.Generated.periodMinimal')
    result['separating_period_proof'] = dict(proof=f'proofs/{receipt.name}',
                                             verification_seconds=perf_counter()-start)
    return result
