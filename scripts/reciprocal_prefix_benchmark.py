"""Run both reciprocal projections and certify any exact singleton factor."""
from time import perf_counter

from experiments.reciprocal_prefix_pairs import measure


def prefix_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    work = measure(n, case['depth'], case['modulus'])
    elapsed = perf_counter() - start
    factors = work['exact_singletons']
    divisor = next((x for x in factors if 1 < x < n), None)
    work['modulus'] = case['modulus']
    for key in ('largest_interval', 'candidates', 'remaining', 'eliminated'):
        work[key] = str(work[key])
    work['exact_singletons'] = list(map(str, factors))
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    return certify_split(case, proof, divisor, elapsed, 'reciprocal_prefix_pairs', work)
