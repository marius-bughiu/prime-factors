"""Compare two certified radix rules with identical CRT lists and square tests."""

import argparse
import json
import platform
from statistics import median
from time import perf_counter

from .affine_radix_holdout import ROOT, draw_prime
from .midpoint_slope_batches import search
from scripts.factor import render_certificate, verify_file


def compare(row, repetitions, rotate):
    n = int(row['n'])
    expected = [row['factors']] if row['factors'] else []
    modes = [(shape+('_curve' if curve else ''), shape, curve)
             for curve in (False, True) for shape in ('rectangle', 'hexagon', 'hexagon_slope')]
    times = {name: [] for name, _, _ in modes}
    reports = {}
    for i in range(repetitions):
        if repetitions == 2:
            order = modes if i == 0 else list(reversed(modes))
        else:
            j = (rotate+i) % len(modes)
            order = modes[j:]+modes[:j]
        for name, geometry, curve in order:
            start = perf_counter()
            result = search(n, geometry=geometry, curve=curve, max_half_entries=65536)
            times[name].append(perf_counter()-start)
            if result.pop('pairs') != expected or (expected and result['remaining_orbits']):
                raise ArithmeticError('the benchmark result disagrees with the reference pair')
            reports[name] = result
    for name in times:
        reports[name].update(seconds=times[name], median_seconds=median(times[name]))
    return dict(n=str(n), expected_factors=row['factors'], repetitions=repetitions, methods=reports)


def new_holdout():
    seed = b'hex-radix-slope-holdout-v1'
    rows, i = [], 0
    while len(rows) < 8:
        p, q = sorted(draw_prime(side, i, bits=25, seed=seed) for side in (b'p', b'q'))
        i += 1
        if p != q:
            row = dict(n=str(p*q), factors=[str(p), str(q)])
            rows.append(dict(sample=i-1, **compare(row, 5, len(rows))))
    return dict(seed=seed.decode(), rows=rows)


def run():
    frozen = json.loads((ROOT/'research/midpoint-weight-holdout.json').read_text())
    extra = json.loads((ROOT/'benchmarks/midpoint-weights.json').read_text())
    selected = {r['id']: r for r in extra}
    return dict(seed=frozen['seed'], platform=platform.platform(), python=platform.python_version(),
                max_half_entries=65536, rows=[compare(row, 5, i) for i, row in enumerate(frozen['rows'])],
                complete_82=compare(selected['midpoint-weights-82'], 2, 0),
                capped_2048=compare(selected['midpoint-weights-capped-2048'], 3, 0),
                fresh=new_holdout())


def verify_fresh(report):
    directory = ROOT/'build'/'hex-weight-holdout'
    directory.mkdir(parents=True, exist_ok=True)
    for row in report['fresh']['rows']:
        path = directory/f"case-{row['sample']}.lean"
        path.write_text(render_certificate(int(row['n']), list(map(int, row['expected_factors']))))
        verify_file(path)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', help='check Lean certificates for the fresh sample')
    args = parser.parse_args()
    report = run()
    if args.verify:
        verify_fresh(report)
    print(json.dumps(report, indent=2))
