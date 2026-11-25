"""Compare the old and curved intervals with identical weights and orbit order."""

import json
from pathlib import Path
import platform
from statistics import median
from time import perf_counter

from .midpoint_weights import search

ROOT = Path(__file__).resolve().parents[1]


def compare(n, factors, orbits, reduce_discriminant, repetitions, offset):
    methods = ('rectangle', 'curve')
    times = {name: [] for name in methods}
    outputs = {}
    for i in range(repetitions):
        order = methods if (i+offset) % 2 == 0 else methods[::-1]
        for method in order:
            start = perf_counter()
            result = search(n, orbits, reduce_discriminant=reduce_discriminant, curve=(method == 'curve'))
            times[method].append(perf_counter()-start)
            if result['pairs'] != ([factors] if factors else []):
                raise ArithmeticError(f'unexpected factor pairs on {n} with {method}')
            outputs[method] = result
    for key in ('radix', 'total_orbits', 'weight_choices', 'gauss_iterations',
                'visited_orbits', 'remaining_orbits', 'table_entries'):
        if outputs['rectangle'][key] != outputs['curve'][key]:
            raise ArithmeticError(f'comparison changed {key} on {n}')
    for method in methods:
        outputs[method]['seconds'] = times[method]
        outputs[method]['median_seconds'] = median(times[method])
    return dict(n=str(n), expected_factors=factors, max_orbits=orbits,
                reduce_discriminant=reduce_discriminant, repetitions=repetitions, **outputs)


def run():
    rows = json.loads((ROOT / 'research/midpoint-weight-holdout.json').read_text())['rows']
    fixed = json.loads((ROOT / 'benchmarks/midpoint-weights.json').read_text())
    holdout = [compare(int(row['n']), row['factors'], None, False, 5, i) for i, row in enumerate(rows)]
    record = {row['id']: row for row in fixed}
    ordinary = record['midpoint-weights-82']
    full = record['midpoint-weights-capped-2048']
    return dict(platform=platform.platform(), python=platform.python_version(),
                seed='midpoint-weight-holdout-v1', holdout=holdout,
                complete_82=compare(int(ordinary['n']), ordinary['factors'], None, False, 2, 0),
                capped_2048=compare(int(full['n']), full['factors'], 128, True, 3, 1))


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
