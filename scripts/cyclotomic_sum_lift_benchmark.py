"""Replay the public fifth-order probe and certify the measured witness or failed probe."""

from time import perf_counter

from experiments import cyclotomic_sum_lift
from scripts.factor import verify_file


def cyclotomic_sum_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    factor, work = cyclotomic_sum_lift.search(n, case['max_tests'])
    elapsed = perf_counter()-start
    agree(dict(id=case['id'], **case['work_checks']), work, case['work_checks'])
    if 'comparison_cap' in case:
        if work['outcome'] != 'sum_square':
            raise ValueError('comparison requires a successful order and sum readout')
        start = perf_counter()
        comparison = cyclotomic_sum_lift.comparisons(n, case['comparison_cap'])
        comparison_seconds = perf_counter()-start
        for mode in ('ordinary', 'trial'):
            expected = case['comparison_checks'][mode]
            agree(dict(id=case['id'], **expected), comparison[mode], expected)
            if comparison[mode]['factor'] != str(factor):
                raise ValueError('comparison did not recover the same divisor')
        work.update(comparison=comparison, comparison_seconds=comparison_seconds)

    result = certify_split(case, proof, factor, elapsed, 'cyclotomic_sum_lift', work)
    if work['outcome'] not in ('sum_square', 'no_order_witness'):
        return result
    base, remainder = work['base'], work['residue']
    theorem = 'PrimeFactors.Generated.fifthOrderProbe'
    # A failed probe certifies this one base only; the original cofactor stays unresolved.
    if factor is None:
        proof.write_text('import Mathlib.Tactic\n')
    with proof.open('a') as source:
        source.write(f'''
theorem {theorem} :
    ({base}:ℕ)^4 ≤ {n} ∧ {n} < ({base}+1)^4 ∧ {base}^5 % {n} = {remainder} := by
  decide +kernel

#print axioms {theorem}
''')
    start = perf_counter()
    verify_file(proof, theorem)
    work['probe_certificate'] = dict(proof=f'proofs/{proof.name}',
                                     verification_seconds=perf_counter()-start)
    return result
