"""Time CRT slope batches and ordinary midpoint weights on the same fixed inputs."""

import json
import platform
from statistics import median
from time import perf_counter

from .affine_radix_holdout import ROOT, draw_prime
from .midpoint_slope_batches import search as batched
from .midpoint_weights import search as ordinary


def compare(n, expected, multipliers, repetitions, offset):
    methods = [0, *multipliers]
    times = {m: [] for m in methods}
    reports = {}
    for i in range(repetitions):
        cut = (offset+i) % len(methods)
        for m in methods[cut:]+methods[:cut]:
            start = perf_counter()
            run = batched(n, multiplier=m) if m else ordinary(n)
            times[m].append(perf_counter()-start)
            if run.pop('pairs') != [expected] or run['remaining_orbits']:
                raise ValueError('complete search disagreed with the independent prime labels')
            reports[m] = run
    return {('ordinary' if not m else f'radix_x{m}'):
            dict(result=reports[m], seconds=times[m], median_seconds=median(times[m])) for m in methods}


def run():
    rows, sample = [], 0
    seed = b'midpoint-weight-holdout-v1'
    while len(rows) < 8:
        p, q = sorted(draw_prime(side, sample, bits=25, seed=seed) for side in (b'p', b'q'))
        sample += 1
        if p != q:
            n, labels = p*q, [str(p), str(q)]
            rows.append(dict(n=str(n), factors=labels, sample=sample-1,
                             methods=compare(n, labels, (1, 2, 3, 4), 5, len(rows))))
    case = next(c for c in json.loads((ROOT/'benchmarks/midpoint-weights.json').read_text())
                if c['id'] == 'midpoint-weights-82')
    large = dict(n=case['n'], factors=case['factors'],
                 methods=compare(int(case['n']), case['factors'], (1,), 3, 0))
    return dict(seed=seed.decode(), python=platform.python_version(), platform=platform.platform(),
                repetitions=5, rows=rows, large=large)


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
