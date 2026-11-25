"""Compare both modular-hyperbola radices and odd trial division on eight prime pairs."""

import argparse
import hashlib
import json
from math import isqrt
from pathlib import Path
from statistics import median
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.modular_hyperbola import search
from scripts.factor import render_certificate, verify_file


def draw_prime(side, sample):
    prefix = b'affine-radix-holdout-v1\0' + side + sample.to_bytes(8, 'big')
    counter = 0
    while True:
        digest = hashlib.shake_256(prefix + counter.to_bytes(8, 'big')).digest(3)
        p = (int.from_bytes(digest, 'big') & ((1 << 23)-1)) | (1 << 22) | 1
        if all(p % d for d in range(3, isqrt(p)+1, 2)):
            return p
        counter += 1


def trial_search(n):
    first = max(2, isqrt((n - 1) // 2) + 1) | 1
    candidates = range(first, isqrt(n) + 1, 2)
    pairs = [[str(x), str(n // x)] for x in candidates if n % x == 0]
    return dict(pairs=pairs, divisor_tests=len(candidates))


def run():
    rows = []
    sample = 0
    while len(rows) < 8:
        p, q = sorted(draw_prime(side, sample) for side in (b'p', b'q'))
        sample += 1
        if p == q:
            continue
        n = p*q
        row = dict(n=str(n), factors=[str(p), str(q)])
        methods = ('binary', 'primorial', 'trial')
        timings = {method: [] for method in methods}
        for repetition in range(5):
            offset = (len(rows) + repetition) % len(methods)
            for method in methods[offset:] + methods[:offset]:
                start = perf_counter()
                report = trial_search(n) if method == 'trial' else search(n, radix_policy=method)
                timings[method].append(perf_counter()-start)
                if report['pairs'] != [row['factors']]:
                    raise ValueError(f'incorrect factors at sample {sample-1}')
                keys = ('divisor_tests',) if method == 'trial' else (
                    'radix', 'low_classes', 'range_counts', 'euclidean_steps', 'modular_hits',
                    'digit_tests', 'selection_tests', 'radix_divisibility_tests')
                row[method] = {k: report[k] for k in keys}
        for method, samples in timings.items():
            row[method]['seconds'] = samples
            row[method]['median_seconds'] = median(samples)
        rows.append(row)
    return rows


def verify(rows):
    directory = ROOT / 'build' / 'affine-radix-holdout'
    directory.mkdir(parents=True, exist_ok=True)
    for i, row in enumerate(rows):
        source = directory / f'case-{i}.lean'
        source.write_text(render_certificate(int(row['n']), [int(p) for p in row['factors']]))
        verify_file(source)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', help='check all eight factorizations with Lean')
    args = parser.parse_args()
    rows = run()
    if args.verify:
        verify(rows)
    print(json.dumps(rows, indent=2))
