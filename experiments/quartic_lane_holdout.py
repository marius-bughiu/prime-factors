"""Compare complete quartic, linear midpoint and trial searches on independent 16-bit prime pairs."""

import argparse
from collections import Counter
from itertools import islice
import json
from math import isqrt
import platform
from statistics import median
from time import perf_counter

from .affine_radix_holdout import ROOT, draw_prime, trial_search
from .midpoint_weights import residue_pairs, search as linear_search
from .quartic_factor_lanes import parameters, search as quartic_search
from scripts.factor import render_certificate, verify_file


SEED = b'quartic-lane-holdout-v1'


def complete_sample():
    methods = [('quartic', quartic_search), ('linear', linear_search), ('trial', trial_search)]
    rows, i = [], 0
    while len(rows) < 8:
        p, q = sorted(draw_prime(side, i, bits=16, seed=SEED) for side in (b'p', b'q'))
        i += 1
        if p == q:
            continue
        n, expected = p*q, [[str(p), str(q)]]
        reports, timings = {}, {name: [] for name, _ in methods}
        for rep in range(3):
            j = (len(rows)+rep) % len(methods)
            for name, search in methods[j:]+methods[:j]:
                start = perf_counter()
                run = search(n)
                timings[name].append(perf_counter()-start)
                if run.pop('pairs') != expected or run.get('remaining_orbits', 0):
                    raise ArithmeticError(f'{name} disagreed with the complete balanced factorization')
                reports[name] = run
        for name, seconds in timings.items():
            reports[name].update(seconds=seconds, median_seconds=median(seconds))
        rows.append(dict(sample=i-1, n=str(n), expected_factors=expected[0], methods=reports))
    return rows


def control(n, cap=4):
    """Record exact coordinate ranges and independently replay every prefix from one through cap."""
    hi, radix = parameters(n)
    lo = max(2, isqrt((n-1)//2)+1)
    _, representatives = residue_pairs(n, radix, Counter())
    lanes = []
    for u, w in islice(representatives, cap):
        first, last = -((u-lo)//radix), (hi-u)//radix
        lanes.append(dict(u=str(u), w=str(w), low_k=str(first), high_k=str(last),
                          possible_coordinates=str(max(0, last-first+1))))
    prefixes = []
    for limit in range(1, cap+1):
        row = dict(max_orbits=limit)
        for name, search in (('quartic', quartic_search), ('linear', linear_search)):
            start = perf_counter()
            run = search(n, limit)
            run['seconds'] = perf_counter()-start
            if run['pairs'] or run['visited_orbits'] != limit or not run['remaining_orbits']:
                raise ArithmeticError(f'unexpected capped {name} result')
            row[name] = run
        prefixes.append(row)
    return dict(n=str(n), lower=str(lo), upper=str(hi), span=str(hi-lo+1), lanes=lanes, prefixes=prefixes)


def run():
    fixture = json.loads((ROOT/'benchmarks/midpoint-weights.json').read_text())
    crossed = next(case for case in fixture if case['id'] == 'midpoint-weights-capped-2048')
    return dict(seed=SEED.decode(), prime_bits=16, repetitions=3,
                platform=platform.platform(), python=platform.python_version(),
                rows=complete_sample(), crossed_2048=control(int(crossed['n'])))


def verify(report):
    folder = ROOT/'build'/'quartic-lane-holdout'
    folder.mkdir(parents=True, exist_ok=True)
    for row in report['rows']:
        path = folder/f"sample-{row['sample']}.lean"
        path.write_text(render_certificate(int(row['n']), list(map(int, row['expected_factors']))))
        verify_file(path)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', help='check all eight prime-factor certificates in Lean')
    args = parser.parse_args()
    report = run()
    if args.verify:
        verify(report)
    print(json.dumps(report, indent=2))
