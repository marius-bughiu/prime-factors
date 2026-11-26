"""Replay a lifted wheel and compare its complete caps with the optimal unsliced full-period split."""

from time import perf_counter

from experiments.factor_sum_quantile import sum_bounds
from experiments.lifted_period_holdout import refined_full_period
from experiments.lifted_period_join import search
from experiments.streamed_sum_join import search as full_period_search


def lifted_period_case(case, proof, agree, certify_split):
    n = int(case['n'])
    interval = None
    if 'factor_bits' in case:
        lower, _, upper = sum_bounds(n, case['factor_bits'])
        interval = lower, upper
    options = dict(max_right=case['max_right'], max_visited=case['max_visited'],
                   max_lookups=case['max_lookups'], sum_interval=interval, reverse=True)
    start = perf_counter()
    run = search(n, **options)
    elapsed = perf_counter() - start
    agree(case, run, ('outcome', 'probes'))
    agree(dict(id=case['id'], **case['work_checks']), run['work'], case['work_checks'])
    reported = run['feasible_plan'] or run['best_plan']
    agree(dict(id=case['id'], **case['plan_checks']), reported, case['plan_checks'])
    # Request only the full-period optimizer's plan; do not charge it with scanning absent rows.
    compared = full_period_search(n, max_right=options['max_right'], max_visited=0,
                                  folded=True, memory_partition=True, sum_interval=interval)
    reference = compared['work']['partition']
    ordinary = dict(right_entries=reference['stored'], left_rows=reference['left_rows'],
                    optimal=reference['optimal'], right_built=compared['work']['right_built'])
    agree(dict(id=case['id'], **case['ordinary_checks']), ordinary, case['ordinary_checks'])
    run['original_full_period'] = ordinary
    # A complete-period folded wheel has at most two wrap lookups per visited row.
    visit_cap = min(options['max_visited'], options['max_lookups'] // 2)
    if 'greedy_checks' in case:
        start = perf_counter()
        greedy = full_period_search(n, max_right=options['max_right'], max_visited=visit_cap,
                                    folded=True, reverse=True, sum_interval=interval)
        seconds = perf_counter() - start
        work = greedy['work']
        measured = dict(outcome=greedy['outcome'], factors=greedy['factors'], seconds=seconds,
                        right_entries=work['right_potential'], left_rows=work['left_potential'],
                        lookup_bound=2 * work['left_potential'], visit_cap=visit_cap,
                        **{key: work[key] for key in ('right_built', 'left_visited', 'lookups', 'square_tests')})
        agree(dict(id=case['id'], **case['greedy_checks']), measured, case['greedy_checks'])
        if greedy['factors'] and greedy['factors'] != run['factors']:
            raise ValueError('the original greedy run returned different factors')
        run['original_greedy_run'] = measured
    if 'refined_checks' in case:
        start = perf_counter()
        refined = refined_full_period(n, *interval, options['max_right'],
                                      options['max_visited'], options['max_lookups'])
        refined['seconds'] = perf_counter() - start
        agree(dict(id=case['id'], **case['refined_checks']), refined, case['refined_checks'])
        if refined['factors'] and refined['factors'] != run['factors']:
            raise ValueError('the refined full-period prefix returned different factors')
        run['refined_full_period'] = refined
        memory = full_period_search(n, max_right=options['max_right'], max_visited=visit_cap,
                                    folded=True, memory_partition=True, reverse=True, sum_interval=interval)
        memory_work = memory['work']
        measured = dict(outcome=memory['outcome'], factors=memory['factors'],
                        **{key: memory_work[key] for key in ('right_built', 'left_visited', 'left_unvisited',
                                                             'lookups', 'square_tests')})
        agree(dict(id=case['id'], **case['memory_prefix_checks']), measured, case['memory_prefix_checks'])
        run['original_memory_prefix'] = measured
    if 'strong_reference_checks' in case:
        start = perf_counter()
        reference = search(n, **options, full_period_only=True)
        measured = dict(seconds=perf_counter() - start, outcome=reference['outcome'],
                        plan=reference['feasible_plan'], work=reference['work'])
        agree(dict(id=case['id'], **case['strong_reference_checks']), measured['work'],
              case['strong_reference_checks'])
        if 'strong_reference_outcome' in case:
            agree(dict(id=case['id'], outcome=case['strong_reference_outcome']), reference, ['outcome'])
            measured.update(best_plan=reference['best_plan'], factors=reference['factors'])
        if ((reference['factors'] or 'strong_reference_outcome' not in case)
                and reference['factors'] != run['factors']):
            raise ValueError('the full-period prime-power run returned different factors')
        run['full_period_prime_power_run'] = measured
    if 'origin' in case:
        run['origin'] = case['origin']
    factor = int(run['factors'][0]) if run['factors'] else None
    return certify_split(case, proof, factor, elapsed, 'lifted_period_join', run)
