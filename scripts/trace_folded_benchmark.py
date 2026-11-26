"""Replay the folded right table against ordinary streaming at identical visit and storage caps."""

from math import gcd, isqrt
from time import perf_counter

from experiments.streamed_sum_join import search
from scripts.factor import verify_file


def _certify_mixed_trace(n, run, proof):
    """Check both oriented powers and the complementary nontrivial gcds."""
    work = run['work']
    hit = work['trace_split']
    g = int(run['bases'][0])
    u, y, trace, factor = (int(hit[key]) for key in ('u', 'target', 'trace', 'divisor'))
    lower = isqrt(4*n-1) + 1
    exponent = n + 1 - lower - hit['a'] - work['trace_center'] + hit['k'] * work['period']
    left, right = max(-exponent, 0), max(exponent, 0)
    u_inverse, y_inverse = pow(u, -1, n), pow(y, -1, n)
    other = gcd(u*y-1, n)
    if sorted((factor, other)) != sorted(map(int, run['factors'])):
        raise ValueError('mixed trace gcds do not give the measured factor pair')
    theorem = 'PrimeFactors.Generated.foldedTraceSplit'
    with proof.open('a', encoding='utf-8') as file:
        file.write(f'''
theorem {theorem} :
    ({g} : ZMod {n})^{hit['t']} = {u} ∧
    ({g} : ZMod {n})^{left}*{y} = {g}^{right} ∧
    ({u}*{u_inverse})%{n} = 1 ∧ ({y}*{y_inverse})%{n} = 1 ∧
    ({u}+{u_inverse})%{n} = {trace} ∧ ({y}+{y_inverse})%{n} = {trace} ∧
    {u} ≠ {y} ∧ ({u}*{y})%{n} ≠ 1 ∧
    Nat.gcd (({u}-{y})+({y}-{u})) {n} = {factor} ∧
    Nat.gcd ({u}*{y}-1) {n} = {other} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · reduce_mod_char
  · reduce_mod_char
  all_goals decide +kernel

#print axioms {theorem}
''')
    start = perf_counter()
    verify_file(proof, theorem)
    return dict(theorem=theorem, complementary_factor=str(other),
                verification_seconds=perf_counter()-start)


def _ordinary(n, options):
    start = perf_counter()
    result = search(n, **options)
    elapsed = perf_counter() - start
    work = result['work']
    return dict(outcome=result['outcome'], factors=result['factors'], seconds=elapsed,
                max_right=options['max_right'], max_visited=options['max_visited'],
                right_potential=work['right_potential'], right_built=work['right_built'],
                left_visited=work['left_visited'], square_tests=work['square_tests'],
                signature_multiplications=work['signature_multiplications'])


def trace_folded_case(case, proof, agree, certify_split):
    n = int(case['n'])
    options = dict(candidates=tuple(map(int, case['bases'])), max_right=case['max_right'],
                   max_visited=case['max_visited'], reverse=case['reverse'])
    start = perf_counter()
    run = search(n, **options, folded=True)
    discovery_seconds = perf_counter() - start
    if 'origin' in case:
        run['origin'] = case['origin']
    agree(case, run, ('outcome', 'probes'))
    agree(dict(id=case['id'], **case['work_checks']), run['work'], case['work_checks'])
    baseline = _ordinary(n, options)
    agree(dict(id=case['id'], **case['baseline_checks']), baseline, case['baseline_checks'])
    run['ordinary'] = baseline
    if 'reference_max_right' in case:
        larger = _ordinary(n, dict(options, max_right=case['reference_max_right']))
        if (not larger['factors'] or larger['factors'] != run['factors'] or
                larger['left_visited'] != run['work']['left_visited']):
            raise ValueError('the larger ordinary table failed to reproduce the same split and row')
        run['ordinary_larger_table'] = larger

    factor = int(run['factors'][0]) if run['factors'] else None
    result = certify_split(case, proof, factor, discovery_seconds, 'trace_folded_right', run)
    if run['outcome'] == 'trace_mixed_gcd':
        run['mixed_certificate'] = _certify_mixed_trace(n, run, proof)
    return result
