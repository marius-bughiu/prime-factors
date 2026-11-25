"""Choose a unimodular offset frame by its product-only modular density."""

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from math import gcd, isqrt
from pathlib import Path
from statistics import median
from time import perf_counter

from experiments.grouped_offset_rows import bounded_rows, ceil_div, direct, discriminant, frame, local_failures
from scripts.factor import primes_through

ROOT = Path(__file__).resolve().parents[1]
SCORE_PRIMES = tuple(primes_through(251))
FULL_IDS = ('grouped-norm-fresh-2048', 'grouped-norm-crossed-2048')


def coordinate_bounds(T, h, limit, basis):
    """The same conservative bounds used to size the row counter's arrays."""
    A, B, C, _ = basis
    first = h//T+1
    if first > limit:
        return 0, 0, 0
    e = B*T-h*A
    low = ceil_div(min(e*first, e*limit)-B*h, h)
    high = (max(e*first, e*limit)-B)//h
    extent = max(abs(low), abs(high))
    return extent, (limit+abs(C)*extent)//B, high-low+1


def changes(radius):
    for i, j, k, l in product(range(-radius, radius+1), repeat=4):
        if i*l-j*k == 1:
            yield i, j, k, l


def change_basis(basis, change):
    A, B, C, D = basis
    i, j, k, l = change
    return i*A+k*D, i*B+k*C, j*B+l*C, j*A+l*D


def obstructions(coefficient, primes):
    """Least obstructing p-power per prime; zero denotes no obstruction."""
    result = []
    for p in primes:
        ordinary, higher = local_failures(coefficient, [p], max(p, 8)*max(1, abs(coefficient)))
        powers = ordinary or higher
        result.append(powers[0] if powers else 0)
    return tuple(result)


def primitive_density(t_fail, r_fail, primes=SCORE_PRIMES):
    """Exact fraction in the finite CRT period, conditioned on primitivity there."""
    numerator = denominator = 1
    for p, t_power, r_power in zip(primes, t_fail, r_fail):
        largest = max(t_power, r_power)
        if not largest:
            continue
        local_den = (p+1)*largest
        forbidden = sum(p*(largest//power) for power in (t_power, r_power) if power)
        numerator *= local_den-forbidden
        denominator *= local_den
    return Fraction(numerator, denominator)


def check_score_period():
    """Count a complete small CRT period, including two higher-power exclusions."""
    t_fail, r_fail, primes = (8, 3, 5), (4, 9, 0), (2, 3, 5)
    primitive = good = 0
    for r, t in product(range(360), repeat=2):
        if gcd(gcd(r, t), 30) != 1:
            continue
        primitive += 1
        good += all(t % q for q in t_fail) and all(r % q for q in r_fail if q)
    if Fraction(good, primitive) != primitive_density(t_fail, r_fail, primes):
        raise AssertionError('exact score disagrees with a complete CRT period')


def choose_frame(T, h, limit, radius=4, *, cost_constrained=False):
    if min(T, h, limit, radius) <= 0:
        raise ValueError('root, residual offset, limit and change radius must be positive')
    original = frame(T, h, limit)[:4]
    cap = 8*(1+isqrt(limit-1))
    _, original_prefix, original_rows = coordinate_bounds(T, h, limit, original)
    best = None
    tested = 0

    @lru_cache(maxsize=None)
    def axis(j, k):
        return obstructions(discriminant(T, h, j, k), SCORE_PRIMES)

    def score(basis):
        A, B, C, D = basis
        # Simultaneously negating a direction preserves its quadratic value.
        return primitive_density(axis(B, A), axis(C, D) if C >= 0 else axis(-C, -D))

    original_score = score(original)
    for change in changes(radius):
        candidate = change_basis(original, change)
        if candidate[1] <= 0:
            continue
        extent, prefix, rows = coordinate_bounds(T, h, limit, candidate)
        if max(extent, prefix) > cap:
            continue
        if cost_constrained and (rows > original_rows or prefix > 2*original_prefix):
            continue
        tested += 1
        key = (score(candidate), rows, prefix, change)
        if best is None or key < best[0]:
            best = (key, candidate)
    if best is None:
        _, prefix, rows = coordinate_bounds(T, h, limit, original)
        density, change, basis = original_score, (1, 0, 0, 1), original
    else:
        (density, rows, prefix, change), basis = best
    return dict(basis=basis, change=change, density=density, original=original,
                original_density=original_score, eligible=tested, axes=axis.cache_info().currsize,
                cap=cap, row_span=rows, max_abs_r=prefix)


def compare(n, limit, rounds, *, check_direct=False, cost_constrained=False):
    """Alternate scan order. Recompute and charge selection on each paired round."""
    T = isqrt(n)
    h = n-T*T
    times = {key: [] for key in ('selection', 'original', 'chosen', 'chosen_total')}
    reports = {}
    for i in range(rounds):
        start = perf_counter()
        selected = choose_frame(T, h, limit, cost_constrained=cost_constrained)
        selection_time = perf_counter()-start
        times['selection'].append(selection_time)
        order = ('original', 'chosen') if i % 2 == 0 else ('chosen', 'original')
        for name in order:
            start = perf_counter()
            basis = None if name == 'original' else selected['basis']
            # A selector abstention uses the existing method and its original memory guard.
            max_prefix = 8_000_000 if name == 'original' or not selected['eligible'] else selected['cap']
            result = bounded_rows(T, h, limit, None, basis=basis, max_prefix=max_prefix)
            elapsed = perf_counter()-start
            times[name].append(elapsed)
            if name == 'chosen':
                times['chosen_total'].append(elapsed+selection_time)
            if result['both_axes'] is None:
                raise ValueError('baseline or selected frame exceeds prefix allowance')
            keys = ('raw', 'primitive', 'first_axis', 'both_axes', 'rows', 'rows_rejected')
            counts = {key: result[key] for key in keys}
            if reports.setdefault(name, counts) != counts:
                raise AssertionError('counts changed between timing rounds')
    if reports['original']['primitive'] != reports['chosen']['primitive']:
        raise AssertionError('frame changed the primitive point count')
    if check_direct:
        hits = []
        for name, basis in [('original', None), ('chosen', selected['basis'])]:
            expected, squares = direct(T, h, limit, None, basis=basis)
            if expected != [reports[name][key] for key in ('raw', 'primitive', 'first_axis', 'both_axes')]:
                raise AssertionError('row count disagrees with individual offsets')
            hits.append(squares)
        if hits[0] != hits[1]:
            raise AssertionError('frame changed the number of exact squares')
        reports['square_hits'] = hits[0]
    return dict(limit=limit, rounds=rounds, cost_constrained=cost_constrained,
                selection={k: str(v) if isinstance(v, Fraction) else v for k,v in selected.items()},
                counts=reports, median_seconds={k: median(v) for k,v in times.items()}, times=times)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--holdout', action='store_true', help='verify eight smaller products by direct enumeration')
    parser.add_argument('--cost-constrained', action='store_true', help='cap row span and prefix relative to original')
    parser.add_argument('--rounds', type=int, default=3)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be at least one')
    if args.holdout:
        check_score_period()
        rows = json.loads((ROOT/'research/quartic-lane-holdout.json').read_text())['rows']
        for row in rows:
            result = compare(int(row['n']), 1<<12, args.rounds, check_direct=True,
                             cost_constrained=args.cost_constrained)
            print(json.dumps(dict(id=row['sample'], **result)), flush=True)
    else:
        rows = json.loads((ROOT/'benchmarks/grouped-norm.json').read_text())
        for name in FULL_IDS:
            row = next(row for row in rows if row['id'] == name)
            result = compare(int(row['n']), 1<<40, args.rounds, cost_constrained=args.cost_constrained)
            print(json.dumps(dict(id=name, **result)), flush=True)


if __name__ == '__main__':
    main()
