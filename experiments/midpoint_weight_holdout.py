"""Compare complete balanced searches on eight fresh 25-bit prime pairs."""

import argparse
import json
import platform
from statistics import median
from time import perf_counter

from .affine_radix_holdout import ROOT, draw_prime, trial_search
from .midpoint_weights import search
from .modular_hyperbola import search as hyperbola
from scripts.factor import render_certificate, verify_file


def run(verify=False):
    methods = ('weights', 'reduced', 'hyperbola', 'trial')
    rows, sample = [], 0
    while len(rows) < 8:
        p, q = sorted(draw_prime(side, sample, bits=25, seed=b'midpoint-weight-holdout-v1')
                      for side in (b'p', b'q'))
        sample += 1
        if p == q:
            continue
        n = p*q
        row = dict(sample=sample-1, n=str(n), factors=[str(p), str(q)])
        times = {name: [] for name in methods}
        for repetition in range(5):
            offset = (len(rows)+repetition) % len(methods)
            for name in methods[offset:] + methods[:offset]:
                start = perf_counter()
                if name in ('weights', 'reduced'):
                    report = search(n, reduce_discriminant=(name == 'reduced'))
                elif name == 'hyperbola':
                    report = hyperbola(n, radix_policy='primorial')
                else:
                    report = trial_search(n)
                times[name].append(perf_counter()-start)
                if report.pop('pairs') != [row['factors']]:
                    raise ValueError(f'{name} returned an incorrect pair on sample {sample-1}')
                row[name] = report
        for name in methods:
            row[name].update(seconds=times[name], median_seconds=median(times[name]))
        if verify:
            path = ROOT / 'build' / 'midpoint-weight-holdout' / f'case-{sample-1}.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(render_certificate(n, [p, q]))
            verify_file(path)
        rows.append(row)
    return dict(seed='midpoint-weight-holdout-v1', prime_bits=25, repetitions=5,
                platform=platform.platform(), python=platform.python_version(), rows=rows)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true')
    print(json.dumps(run(parser.parse_args().verify), indent=2))
