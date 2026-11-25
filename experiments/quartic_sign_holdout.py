"""Compare signed and positive quartic lanes on identical products and residue pairs."""

from collections import Counter
from itertools import islice
import json
from math import isqrt
import platform
from statistics import median
from time import perf_counter

from .affine_radix_holdout import ROOT
from .midpoint_weights import residue_pairs
from .quartic_factor_lanes import pairs_in_windows, parameters, search, signed_orbit_count, signed_representatives


def compare_complete(row, index):
    times = {'positive': [], 'signed': []}
    reports = {}
    for repetition in range(3):
        modes = ('positive', 'signed') if (index+repetition)%2 == 0 else ('signed', 'positive')
        for mode in modes:
            start = perf_counter()
            result = search(int(row['n']), signed=(mode == 'signed'))
            times[mode].append(perf_counter()-start)
            if result.pop('pairs') != [row['expected_factors']] or result['remaining_orbits']:
                raise ArithmeticError('complete searches disagree with the certified factor pair')
            reports[mode] = result
    if reports['positive']['total_orbits'] != reports['signed']['ordinary_covered_orbits']:
        raise ArithmeticError('the signed comparison did not cover every positive pair')
    for mode, seconds in times.items():
        reports[mode].update(seconds=seconds, median_seconds=median(seconds))
    return dict(n=row['n'], expected_factors=row['expected_factors'], **reports)


def matched_prefix(n, groups):
    """Choose the same unordered positive residue pairs for both methods, including fixed pairs."""
    bound, radix = parameters(n)
    lower = isqrt((n-1)//2)+1
    work = Counter()
    ordinary, original = residue_pairs(n, radix, work)
    total = signed_orbit_count(n, radix, ordinary, work)
    reps = list(islice(signed_representatives(original, radix, work), groups))
    jobs = []
    for u, w in reps:
        positive = [(u, w)]
        if radix > 2 and u+w != radix:
            # Negation reverses the first differing CRT digit, so swapping restores the old orientation.
            positive.append(((-w) % radix, (-u) % radix))
        jobs.append(positive)
    results = {}
    for mode in ('positive', 'signed'):
        counts, hits = Counter(), set()
        start = perf_counter()
        for positive in jobs:
            if mode == 'positive':
                for u, w in positive:
                    hits.update(pairs_in_windows(n, u, w, radix, bound, [(lower, bound)], counts, 2))
            else:
                u, w = positive[0]
                bands = [(lower, bound), (-bound, -lower)] if len(positive) == 2 else [(lower, bound)]
                hits.update(pairs_in_windows(n, u, w, radix, bound, bands, counts, 2))
        seconds = perf_counter()-start
        results[mode] = dict(work=dict(counts), seconds=seconds,
                             pairs=[[str(x),str(y)] for x,y in sorted(hits)])
    if results['positive']['pairs'] != results['signed']['pairs']:
        raise ArithmeticError('matched prefix returned different factor pairs')
    return dict(n=str(n), radix=radix, total_signed_orbits=total, total_positive_orbits=ordinary,
                visited_signed_orbits=len(jobs), visited_positive_orbits=sum(map(len,jobs)),
                comparison_orbits=[[[str(u),str(w)] for u,w in job] for job in jobs],
                common_setup_work=dict(work), **results)


def run():
    frozen = json.loads((ROOT/'research/quartic-lane-holdout.json').read_text())
    return dict(seed=frozen['seed'], repetitions=3, python=platform.python_version(), platform=platform.platform(),
                rows=[compare_complete(row, i) for i, row in enumerate(frozen['rows'])],
                matched_2048=matched_prefix(int(frozen['crossed_2048']['n']), 2))


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
