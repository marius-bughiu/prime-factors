"""Check three identical lifted-period joins and certify the recurrence's split."""

from time import perf_counter

from experiments.lifted_period_trace import compare


def lifted_trace_case(case, proof, agree, certify_split):
    start = perf_counter()
    run = compare(int(case['n']), case['factor_bits'], rounds=1, caps=case['caps'])
    run['comparison_seconds'] = perf_counter() - start
    agree(case, run, ('outcome', 'lift', 'period', 'lookup_bound', 'table_sha256'))
    for mode, checks in case['work_checks'].items():
        agree(dict(id=case['id'], **checks), run['methods'][mode], checks)
    times = run['timing_ms']
    discovery_seconds = (times['common_planning'] + times['medians']['recurrence'][2]) / 1_000
    factor = int(run['factors'][0]) if run['factors'] else None
    return certify_split(case, proof, factor, discovery_seconds, 'lifted_period_trace', run)
