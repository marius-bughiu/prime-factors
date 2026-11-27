"""Compare a matched number of square tests and certify a strict extra split."""
from time import perf_counter

from experiments.interior_prime_family import search, search_units
from scripts.factor import render_certificate, verify_file


def equal_six_case(case, proof, agree, certify_split):
    n, budget = int(case['n']), case['budget']
    work = {'budget': budget}
    for name, solver in (('odd', search), ('unit', search_units)):
        start = perf_counter()
        scan = solver(n, budget)
        work[name+'_seconds'] = perf_counter()-start
        f = scan['factor']
        work[name+'_found'] = None if f is None else str(min(f,n//f))
        work[name+'_tests'] = scan['tests']
        work[name+'_squares'] = scan['squares']
    agree({'id': case['id'], **case['checks']}, work, case['checks'])
    if work['odd_found'] is not None and work['unit_found'] is None:
        raise ArithmeticError('filter discarded a proper split')
    result = certify_split(case, proof, None, work['unit_seconds'], 'equal_six_budget', work)
    if work['unit_found'] is None:
        return result
    p = int(work['unit_found'])
    q = n//p
    work['odd_first_split_index'] = (3*p+2*q)//2 - scan['first']//2 + 1
    start = perf_counter()
    source = 'import PrimeFactors.SixTraceBudget\n'+render_certificate(n,[p,q],certificate_trial_limit=2)
    # The two schedules can both succeed on some products. The stronger
    # population theorem is warranted when this product is an extra success.
    if work['odd_found'] is None:
        comparison = f'¬oddHit n first {budget} ∧ successes oddHit {budget} ⊂ successes unitHit {budget}'
        compare_proof = f'''have miss : ¬oddHit n first {budget} :=
    odd_miss_of_endpoint (first:=first) (budget:={budget}) pp qp (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  refine ⟨factorization, by decide +kernel, origin, by decide +kernel, by decide +kernel, hit, miss, ?_⟩
  apply population_strict_at (budget:={budget}) pp qp (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  · rw [origin]; exact hit
  · rw [origin]; exact miss'''
    else:
        comparison = f'oddHit n first {budget}'
        compare_proof = f'''have matched : oddHit n first {budget} :=
    ⟨3*p+2*q, by decide +kernel, by decide +kernel, by decide +kernel,
      min_splits pp qp (by decide +kernel)⟩
  exact ⟨factorization, by decide +kernel, origin, by decide +kernel, by decide +kernel, hit, matched⟩'''
    source += f'''
namespace PrimeFactors.Generated
open SixTraceBudget
private abbrev p : ℕ := {p}
private abbrev q : ℕ := {q}
private abbrev n : ℕ := p*q
private abbrev first : ℕ := {scan['first']}
theorem equalSixBudget :
    ExactFactorization n [p,q] ∧ n={n} ∧ ceilSqrt (24*n)=first ∧
    (3*p+2*q)/2 - first/2 + 1 = {work['odd_first_split_index']} ∧
    unitCount (3*p+2*q) - unitCount first + 1 = {work['unit_tests']} ∧
    unitHit n first {budget} ∧ ({comparison}) := by
  have pp : p.Prime := factorization.2 p (.head _)
  have qp : q.Prime := factorization.2 q (.tail _ (.head _))
  have origin : ceilSqrt (24*n)=first := first_of_squares (n:=n) (f:=first)
    (by decide +kernel) (by decide +kernel)
  have hit : unitHit n first {budget} := unit_hit_at_minimum (first:=first) (budget:={budget}) pp qp
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  {compare_proof}
#print axioms equalSixBudget
end PrimeFactors.Generated
'''
    proof.write_text(source)
    check = perf_counter()
    verify_file(proof,'PrimeFactors.Generated.equalSixBudget')
    result.update(verified=True,status='complete',factors=[str(p),str(q)],remaining=[],
                  verification_seconds=perf_counter()-check, certificate_seconds=perf_counter()-start)
    return result
