"""Check each bounded dilation comparison, then certify a factor if one was found."""
from experiments.primitive_multiplier_traces import SCHEDULES, compare


def primitive_multiplier_case(case, proof, agree, certify_split):
    n = int(case['n'])
    lanes, height = case['lanes'], case['height']
    runs = {mode: compare(n, lanes, height, mode) for mode in SCHEDULES}
    factors = set()
    for mode, run in runs.items():
        factors.update(run['factors'])
        run['factors'] = [str(f) for f in run['factors']]
        checks = case['checks'][mode]
        agree({'id': case['id'], **checks}, run['reduced'], checks)
    work = dict(lanes=lanes, height=height, schedules=runs)
    elapsed = sum(run['reduced_seconds'] for run in runs.values())
    return certify_split(case, proof, min(factors, default=None), elapsed, 'primitive_multiplier', work)
