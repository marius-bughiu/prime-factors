"""Replay a bounded streaming CRT join and its declared full-list comparisons."""

from math import gcd, isqrt
from time import perf_counter

from experiments import streamed_sum_join, sum_signature_join
from scripts.factor import verify_file


def _gap_certificate(n, run, proof):
    """Check the two incorrect matching sums and the measured residual exponent."""
    g = int(run['bases'][0])
    first, second = map(int, run['work']['first_two_sums'])
    gap = abs(second-first)
    reduced = int(run['work']['last_gap']['remaining'])
    residue = pow(g, reduced, n)
    split = gcd(residue-1, n)
    if split not in map(int, run['factors']):
        raise ValueError('the last residual exponent does not expose the measured split')
    d1 = first*first-4*n
    d2 = second*second-4*n
    r1, r2 = isqrt(d1), isqrt(d2)
    if d1 == r1*r1 or d2 == r2*r2:
        raise ValueError('expected two incorrect matching sums')
    theorem = 'PrimeFactors.Generated.streamedGap'
    with proof.open('a') as source:
        source.write(f'''
theorem {theorem} :
    ({g} : ZMod {n})^{first} = {g}^({n}+1) ∧
    ({g} : ZMod {n})^{second} = {g}^({n}+1) ∧
    ({g} : ZMod {n})^{gap} = 1 ∧
    ({r1}:ℕ)^2 < {first}^2-4*{n} ∧ {first}^2-4*{n} < ({r1}+1)^2 ∧
    ({r2}:ℕ)^2 < {second}^2-4*{n} ∧ {second}^2-4*{n} < ({r2}+1)^2 ∧
    ({g} : ZMod {n})^{reduced} = {residue} ∧ Nat.gcd ({residue}-1) {n} = {split} := by
  exact ⟨by reduce_mod_char, by reduce_mod_char, by reduce_mod_char,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by reduce_mod_char, by decide +kernel⟩

#print axioms {theorem}
''')
    start = perf_counter()
    verify_file(proof, theorem)
    return dict(exponent=str(reduced), residue=str(residue), factor=str(split),
                theorem=theorem, verification_seconds=perf_counter()-start)


def streamed_sum_case(case, proof, agree, certify_split):
    n = int(case['n'])
    bases = tuple(map(int, case['bases']))
    options = dict(candidates=bases, max_right=case['max_right'],
                   reverse=case['reverse'], gap_trial_cap=case['gap_trial_cap'])
    start = perf_counter()
    run = streamed_sum_join.search(n, max_visited=case['max_visited'], **options)
    elapsed = perf_counter() - start
    if 'origin' in case:
        run['origin'] = case['origin']
    agree(case, run, ['outcome', 'probes'])
    agree(dict(id=case['id'], **case['work_checks']), run['work'], case['work_checks'])

    if case.get('compare_complete', False):
        start = perf_counter()
        old = sum_signature_join.witnessed_search(
            n, bases, max_half_entries=case['comparison_list_cap'], gap_trial_cap=0)
        old_seconds = perf_counter() - start
        full = old['work']
        left, right = int(full['left_entries']), int(full['right_entries'])
        work = run['work']
        if (min(left, right), max(left, right)) != (work['right_potential'], work['left_potential']):
            raise ValueError('the two planners generated different half lists')
        if old['factors'] != run['factors'] or full['signature_matches'] != 1:
            raise ValueError('the full comparison did not find the same unique sum')
        start = perf_counter()
        opposite = streamed_sum_join.search(
            n, **dict(options, reverse=not case['reverse']), max_visited=work['left_potential'])
        opposite_seconds = perf_counter() - start
        opposite_visits = opposite['work']['left_visited']
        if (opposite['factors'] != run['factors'] or
                opposite_visits + work['left_visited'] != work['left_potential'] + 1):
            raise ValueError('opposite unique-match ranks failed to complement each other')

        # A cap below the larger half stops the earlier planner before allocating either list.
        capped = sum_signature_join.witnessed_search(
            n, bases, max_half_entries=case['max_right'], gap_trial_cap=0)
        comparison = dict(full_list_cap=case['comparison_list_cap'], original_lists=[left, right],
                          full_outcome=old['outcome'], full_matching_sums=full['signature_matches'],
                          full_seconds=old_seconds, same_storage_cap_outcome=capped['outcome'],
                          reverse_visited=opposite_visits, reverse_seconds=opposite_seconds)
        agree(dict(id=case['id'], **case['comparison_checks']), comparison, case['comparison_checks'])
        run['comparison'] = comparison

    factor = int(run['factors'][0]) if run['factors'] else None
    result = certify_split(case, proof, factor, elapsed, 'streamed_sum_join', run)
    if case.get('certify_gap', False):
        run['gap_certificate'] = _gap_certificate(n, run, proof)
    return result
