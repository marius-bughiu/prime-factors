"""Compare signed Newton and exact Taylor quartic searches on the same products."""

import json
import platform
from pathlib import Path
from statistics import median
from tempfile import TemporaryDirectory
from time import perf_counter, process_time

from .affine_radix_holdout import ROOT
from .quartic_factor_lanes import search
from scripts.factor import render_certificate, verify_file


BASES = ('taylor-exact', 'newton')


def compare(n, cap, repetitions, rotation):
    runs = {}
    wall = {basis: [] for basis in BASES}
    cpu = {basis: [] for basis in BASES}
    for repetition in range(repetitions):
        order = BASES if (rotation + repetition) % 2 == 0 else reversed(BASES)
        for basis in order:
            start_wall, start_cpu = perf_counter(), process_time()
            result = search(n, cap, basis=basis, signed=True, power=2)
            cpu[basis].append(process_time() - start_cpu)
            wall[basis].append(perf_counter() - start_wall)
            if basis in runs and result != runs[basis]:
                raise ArithmeticError('the deterministic search changed across repetitions')
            runs[basis] = result
    for basis, result in runs.items():
        result.update(wall_seconds=wall[basis], median_wall_seconds=median(wall[basis]),
                      cpu_seconds=cpu[basis], median_cpu_seconds=median(cpu[basis]))
    return runs


def run():
    frozen = json.loads((ROOT/'research/quartic-lane-holdout.json').read_text())
    rows = []
    with TemporaryDirectory() as temp:
        source = Path(temp)/'Factorization.lean'
        for index, row in enumerate(frozen['rows']):
            n = int(row['n'])
            runs = compare(n, None, 3, index)
            factors = runs['newton']['pairs']
            if factors != [row['expected_factors']]:
                raise ArithmeticError('the Newton search missed the frozen prime pair')
            if any(r['pairs'] != factors or r['remaining_orbits'] or
                   r['ordinary_covered_orbits'] != r['ordinary_total_orbits'] for r in runs.values()):
                raise ArithmeticError('the complete searches disagreed or left unchecked groups')
            source.write_text(render_certificate(n, [int(f) for f in factors[0]]))
            verify_file(source)
            rows.append(dict(sample=row['sample'], n=str(n), certified_factors=factors[0], methods=runs))

    n = int(frozen['crossed_2048']['n'])
    cap = 2
    control = compare(n, cap, 1, 0)
    if any(run['pairs'] or run['visited_orbits'] != cap or not run['remaining_orbits']
           for run in control.values()):
        raise ArithmeticError('the fixed unresolved prefix changed')
    return dict(seed=frozen['seed'], prime_bits=16, signed=True, power=2, repetitions=3,
                python=platform.python_version(), platform=platform.platform(), rows=rows,
                capped_2048=dict(n=str(n), remaining_cofactor=str(n), max_orbits=cap,
                                 repetitions=1, methods=control))


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
