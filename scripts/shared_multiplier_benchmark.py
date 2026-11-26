"""Replay shared-discriminant discovery, independent comparisons and union certificates."""
from math import gcd
from time import perf_counter

from scripts.factor import verify_file

from experiments.shared_multiplier_prefix import search


def shared_multiplier_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    run = search(n, case['k'], case['cap'])
    elapsed = perf_counter()-start
    s,ordinary,local = run['shared'],run['ordinary'],run['ordinary_mod24']
    best = run['widest_mod24']
    widest = s['widest']
    work = dict(k=run['k'],cap=run['cap'],first_trace=str(run['first_trace']),
                first_omitted=str(run['first_omitted']),lower=str(run['lower']),upper=str(run['upper']),
                directions=s['directions'],active_directions=s['active_directions'],interval_count=len(s['intervals']),
                overlapping_positions=str(s['overlapping_positions']),positions=str(s['positions']),
                widest_positions=str(widest['positions'] if widest else 0),widest_a=widest['a'] if widest else None,
                ordinary_positions=str(ordinary['positions']),ordinary_mod24_positions=str(local['positions']),
                widest_mod24_positions=str(best['positions']),
                widest_mod24_a=best['widest']['a'] if best['widest'] else None,
                widest_mod24_plan_directions=best['plan_weights'],widest_mod24_plan_roots=best['plan_hull_roots'],
                widest_mod24_trace_tests=best['work']['trace_square_tests'],
                exact_squares=s['work']['exact_squares'],trace_tests=s['work']['trace_square_tests'],
                unresolved_positions=str(run['remaining_positions']),
                oriented_factor_hits=list(map(str,s['factors'])),shared_gcd_factors=list(map(str,s['gcd_splits'])),
                widest_oriented_hits=list(map(str,s['widest_factors'])),
                ordinary_gcd_factors=list(map(str,ordinary['gcd_splits'])),
                ordinary_mod24_gcd_factors=list(map(str,local['gcd_splits'])),
                widest_mod24_gcd_factors=list(map(str,best['gcd_splits'])),
                divisor_trial_divisions=run['divisor_trial_divisions'], work=s['work'],
                ordinary_work=ordinary['work'],ordinary_mod24_work=local['work'],
                widest_mod24_work=best['work'])
    agree(dict(id=case['id'],**case['checks']),work,case['checks'])
    # A common nontrivial square can give the factor directly, independently
    # of whether it was reached by any particular oriented assignment.
    found = sorted(set(s['gcd_splits']) | set(s['factors']))
    result = certify_split(case,proof,found[0] if found else None,elapsed,'shared_multiplier_prefix',work)
    if s['gcd_splits']:
        s0,d = next((t,h) for t,h in s['squares'] if 1 < gcd((t+h)//2,n) < n)
        g = gcd((s0+d)//2,n)
        factors = '['+', '.join(result['factors'])+']'
        statement = f'''
namespace PrimeFactors.Generated
/-- The checked prefix includes this exact common square and its proper gcd. -/
theorem sharedSplit :
    (({run['first_trace']}-1)^2 < 4*{run['k']}*{n} ∧
      4*{run['k']}*{n} ≤ {run['first_trace']}^2 ∧
      {run['first_trace']} ≤ {s0} ∧ {s0} < {run['first_trace']}+{run['cap']} ∧
      {s0}^2 = 4*{run['k']}*{n}+{d}^2 ∧ Nat.gcd (({s0}+{d})/2) {n} = {g} ∧
      1 < {g} ∧ {g} < {n}) ∧ ExactFactorization {n} {factors} :=
  ⟨by decide +kernel, factorization⟩
#print axioms sharedSplit
end PrimeFactors.Generated
'''
        proof.write_text(proof.read_text()+statement)
        checking = perf_counter()
        verify_file(proof,'PrimeFactors.Generated.sharedSplit')
        extra = perf_counter()-checking
        result['verification_seconds'] += extra
        result['certificate_seconds'] += extra
    if case.get('certify_exclusion'):
        from scripts.weighted_trace_prefix_certificate import check_shared_interval
        if found or s['squares']:
            raise ValueError('requested a no-square union certificate for a positive prefix')
        result['exclusion'] = check_shared_interval(n,run,proof)
    return result
