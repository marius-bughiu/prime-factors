"""Compare four complete searches after freezing a 512-remainder projection budget."""

import argparse
import json
import platform
from math import gcd
from pathlib import Path
from statistics import median
from time import process_time_ns

from experiments.projected_divisor_wheel import PERIOD, allowed, project, search, wheel
from experiments.reciprocal_fermat_holdout import bounds, first_split, inputs


METHODS = ('divisor', 'projected_divisor', 'sum', 'projected_sum')
STEP_LIMIT = 512


def measure(n, bits, method, units, inverses):
    start = process_time_ns()
    constraints = None
    if method.startswith('projected'):
        constraints = project(n, STEP_LIMIT)
        if constraints['setup_factor']:
            return dict(factor=constraints['setup_factor'], setup_hit=True, tests=0,
                        cpu_ns=process_time_ns()-start)
    residues = allowed(constraints['constraints']) if constraints else units
    if method.endswith('sum'):
        sums = sorted({(r + n*inverses[r]) % PERIOD for r in residues})
        pair, tests = first_split(n, *bounds(n, bits), PERIOD, sums)
        factor = pair[0] if pair else None
    else:
        factor, tests = search(n, bits, residues, 1 << bits)
    return dict(factor=str(factor), setup_hit=False, tests=tests, cpu_ns=process_time_ns()-start)


def panel():
    start = process_time_ns()
    units = [r for r in range(1, PERIOD, 2) if gcd(r, PERIOD) == 1]
    fixed_times = dict(units=process_time_ns()-start)
    start = process_time_ns()
    wheel.cache_clear()
    wheel()
    fixed_times['signs'] = process_time_ns()-start
    start = process_time_ns()
    inverses = {r: pow(r, -1, PERIOD) for r in units}
    fixed_times['inverses'] = process_time_ns()-start
    rows = []
    for bits in (20, 24):
        for index, (sample, pair) in enumerate(inputs(bits)):
            n = pair[0]*pair[1]
            methods = {}
            for repeat in range(len(METHODS)):
                offset = (repeat+index) % len(METHODS)
                for method in METHODS[offset:] + METHODS[:offset]:
                    result = measure(n, bits, method, units, inverses)
                    if int(result['factor']) not in pair:
                        raise ArithmeticError('recovered divisor disagrees with the known prime pair')
                    timing = result.pop('cpu_ns')
                    if method not in methods:
                        methods[method] = dict(result, cpu_ns=[])
                    elif any(methods[method][k] != v for k, v in result.items()):
                        raise ArithmeticError('repeated searches disagreed')
                    methods[method]['cpu_ns'].append(timing)
            relation = project(n, STEP_LIMIT)
            rows.append(dict(n=str(n), bits=bits, sample=sample, panel='pilot' if index < 6 else 'validation',
                             factorization=[str(x) for x in pair], relation=relation, methods=methods))
    summaries = []
    for bits in (20, 24):
        for name in ('pilot','validation'):
            subset = [r for r in rows if r['bits']==bits and r['panel']==name]
            measures = {}
            for m in METHODS:
                totals = [sum(r['methods'][m]['cpu_ns'][i] for r in subset) for i in range(len(METHODS))]
                measures[m] = dict(median_batch_cpu_ns=int(median(totals)),
                                   tests=sum(r['methods'][m]['tests'] for r in subset))
            summaries.append(dict(bits=bits, panel=name, methods=measures,
                                  setup_hits=sum(bool(r['relation']['setup_factor']) for r in subset),
                                  rank_gains=sum(r['relation']['projected_rank'] > r['relation']['direct_rank']
                                                 for r in subset)))
    return dict(period=PERIOD, steps=STEP_LIMIT, repetitions=len(METHODS),
                sample='reciprocal-fermat-holdout-v1, first six per width used for choosing the step budget',
                timings='Process CPU nanoseconds, rotating method order; fixed reusable tables measured separately.',
                python=platform.python_version(), machine=platform.machine(), fixed_table_cpu_ns=fixed_times,
                rows=rows, summaries=summaries)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = json.dumps(panel(), indent=2)
    if args.output:
        args.output.write_text(report+'\n')
    else:
        print(report)
