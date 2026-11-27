"""Replay two residue-selected weighted sums with a 34-root budget."""
from time import perf_counter

from experiments.geometry_weight_menu import rule, search


def geometry_weight_case(case, proof, agree, certify_split):
    n = int(case['n'])
    previous, selected = rule(n%24)
    start = perf_counter()
    common, old_hits, new_hits = search(n)
    elapsed = perf_counter()-start
    old_factor = min(common|old_hits, default=None)
    new_factor = min(common|new_hits, default=None)
    union = {}
    for a,b,count in previous+selected:
        union[a,b] = max(union.get((a,b),0),count)
    work = dict(residue=n%24, selected_arms=[list(arm) for arm in selected],
                roots_per_schedule=34, shared_run_roots=17+len(union)+sum(union.values()),
                previous_found=str(old_factor) if old_factor else None,
                selected_found=str(new_factor) if new_factor else None)
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    result = certify_split(case, proof, new_factor, elapsed, 'geometry_weight_menu', work)
    if old_factor and not new_factor:
        path = proof.with_name(proof.stem+'-previous.lean')
        comparison = certify_split(case, path, old_factor, elapsed, 'previous_allocation', work)
        if not comparison['verified'] or comparison['factors'] != case['previous_factors']:
            raise ValueError(f"Incorrect previous-allocation split for {case['id']}")
        work['previous_certificate'] = f'proofs/{path.name}'
        work['previous_factors'] = comparison['factors']
    return result
