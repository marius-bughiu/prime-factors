"""Replay both parts of the factor-sum median cut against the full bounded interval."""

from time import perf_counter

from experiments.factor_sum_quantile import compare


def quantile_case(case, proof, agree, certify_split):
    start = perf_counter()
    runs = compare(int(case['n']), case['factor_bits'], max_right=case['max_right'],
                   max_visited=case['max_visited'])
    elapsed = perf_counter() - start
    for key, expected in case['expect_runs'].items():
        agree(dict(id=case['id'], **expected), runs[key], expected)
    full, inner, outer = runs['full'], runs['inner'], runs['outer']
    if int(inner['positions']) + int(outer['positions']) != int(full['positions']):
        raise ValueError('sum intervals failed to partition the integer search range')
    answers = {tuple(run['factors']) for run in runs.values() if run['factors']}
    if len(answers) > 1:
        raise ValueError('different factorizations returned for the same product')
    factor = int(next(iter(answers))[0]) if answers else None
    work = dict(runs=runs, max_right=case['max_right'], max_visited=case['max_visited'],
                factor_bits=case['factor_bits'])
    return certify_split(case, proof, factor, elapsed, 'factor_sum_quantile', work)
