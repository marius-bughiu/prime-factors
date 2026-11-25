"""Reproduce the first 32 pairs of distinct 17-bit primes and compare searches."""

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

from experiments.class_order_search import is_prime, search
from scripts.factor import render_certificate, verify_file

SEED = 'shared-quadratic-class-orders-v1'


def draw_prime(index, side, exclude=None):
    prefix = SEED.encode() + b'\0' + index.to_bytes(4, 'big') + side
    counter = 0
    while True:
        bits = hashlib.shake_256(prefix + counter.to_bytes(4, 'big')).digest(3)
        p = (int.from_bytes(bits, 'big') % (1 << 17)) | (1 << 16) | 1
        if p != exclude and is_prime(p):
            return p
        counter += 1


def trial(n):
    low = (isqrt((n-1)//2)+1) | 1
    for visits, d in enumerate(range(low, isqrt(n)+1, 2), start=1):
        if n % d == 0:
            return {'factor': d, 'divisor_tests': visits}
    raise ArithmeticError('promised factor missing from balanced interval')


def run():
    rows = []
    for index in range(32):
        p = draw_prime(index, b'p')
        p, q = sorted((p, draw_prime(index, b'q', p)))
        n = p*q
        row = dict(n=str(n), factors=[str(p), str(q)])
        methods = ('shared', 'independent', 'trial')
        timings = {method: [] for method in methods}
        for repetition in range(3):
            offset = (index+repetition) % len(methods)
            for method in methods[offset:]+methods[:offset]:
                start = perf_counter()
                result = trial(n) if method == 'trial' else search(n, 43, 100000, method == 'shared')
                timings[method].append(perf_counter()-start)
                factor = result.pop('factor')
                if factor is not None and factor not in (p, q):
                    raise ArithmeticError(f'wrong factor on input {index}')
                result['found'] = factor is not None
                row[method] = result
        for method, samples in timings.items():
            row[method]['median_seconds'] = median(samples)
        rows.append(row)
    return dict(seed=SEED, prime_bits=17, prime_limit=43, max_compositions=100000, cases=rows)


def verify(report):
    directory = ROOT / 'build' / 'shared-class-orders'
    directory.mkdir(parents=True, exist_ok=True)
    for i, row in enumerate(report['cases']):
        source = directory / f'case-{i}.lean'
        source.write_text(render_certificate(int(row['n']), list(map(int, row['factors']))))
        verify_file(source)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    report = run()
    if args.verify:
        verify(report)
    print(json.dumps(report, indent=2))
