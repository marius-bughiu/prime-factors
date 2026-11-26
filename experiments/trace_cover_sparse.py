"""Certify a minimum giant-block allocation for the full interval of balanced ratios.

The optimizer generates only local interval columns. The verifier checks every
budget on every slope independently of these temporary optimization restrictions.
"""

from argparse import ArgumentParser
from bisect import bisect_left
from fractions import Fraction
from heapq import heappop, heappush
import json
from pathlib import Path
import sys
from time import perf_counter

from .farey_allocation import fast
from .trace_cover import bounded_slopes, cover_cost, envelope, lattice_start, run_allocation


class Ratios:
    """Cache numerators, denominators and their products for exact threshold tests."""

    def __init__(self, points):
        self.coordinates = [(x.numerator, x.denominator, x.numerator*x.denominator)
                            for x in points]

    def extent(self, n, window, block, pivot, budget):
        """Half-open range where the trace lies strictly below the first omitted level."""
        a, b, start, step = window
        threshold = (start + step*block*budget)**2
        lo, hi = 0, pivot
        while lo < hi:
            mid = (lo+hi)//2
            num, den, product = self.coordinates[mid]
            if n*(a*den + b*num)**2 < product*threshold:
                hi = mid
            else:
                lo = mid+1
        first = lo
        lo, hi = pivot, len(self.coordinates)
        while lo < hi:
            mid = (lo+hi)//2
            num, den, product = self.coordinates[mid]
            if n*(a*den + b*num)**2 < product*threshold:
                lo = mid+1
            else:
                hi = mid
        return first, lo


def restricted_cover(n, windows, block, points, caps, max_columns):
    """Solve the sampled interval cover up to the current local budget caps."""
    ratios = Ratios(points)
    starts = [[] for _ in points]
    columns = 0
    for index, (window, cap) in enumerate(zip(windows, caps)):
        pivot = bisect_left(points, Fraction(window[0], window[1]))
        lo, hi = ratios.extent(n, window, block, pivot, cap)
        levels = sorted((cover_cost(n, window, block, points[j]), j) for j in range(lo, hi))
        left, right = hi, lo
        for i, (cost, j) in enumerate(levels):
            left, right = min(left, j), max(right, j+1)
            if i+1 == len(levels) or levels[i+1][0] != cost:
                starts[left].append((right, cost, index))
                columns += 1
        if columns > max_columns:
            raise ValueError('sparse column budget exhausted')

    values, choices, active = [0], [], []
    for j, offers in enumerate(starts):
        for right, cost, index in offers:
            heappush(active, (values[j]+cost, -right, j, index, cost))
        while active and -active[0][1] <= j:
            heappop(active)
        if not active:
            raise ArithmeticError('available columns fail to cover a test ratio')
        value, _, left, index, cost = active[0]
        values.append(value)
        choices.append((left, index, cost))
    budgets = [0]*len(windows)
    j = len(points)
    while j:
        j, index, cost = choices[j-1]
        budgets[index] = max(budgets[index], cost)
    prices = [(x, values[j+1]-values[j]) for j, x in enumerate(points) if values[j+1] > values[j]]
    return budgets, prices, columns


def separate(n, windows, block, prices):
    """Return one violating integer budget per slope, or certify all budgets.

    If F(g) is the total price covered by g, any smaller violation h satisfies
    h < F(h) <= F(g). This skips directly to F(g)-1. All budgets at least the
    total price automatically satisfy the inequality. The loop checks down to 0.
    """
    points = [x for x, _ in prices]
    ratios = Ratios(points)
    prefix = [0]
    for _, weight in prices:
        prefix.append(prefix[-1]+weight)
    violations, probes = [], 0
    for i, window in enumerate(windows):
        pivot = bisect_left(points, Fraction(window[0], window[1]))
        budget = prefix[-1]-1
        while budget >= 0:
            lo, hi = ratios.extent(n, window, block, pivot, budget)
            probes += 1
            paid = prefix[hi]-prefix[lo]
            if paid > budget:
                violations.append((i, budget))
                break
            budget = paid-1
    return violations, probes


def verify_sparse(n, windows, block, left, right, budgets, prices):
    if len(budgets) != len(windows) or any(type(g) is not int or g < 0 for g in budgets):
        raise ValueError('invalid budget vector')
    if not all(left <= x <= right and type(w) is int and w > 0 for x, w in prices):
        raise ValueError('invalid weighted test ratio')
    if prices != sorted(prices) or len({x for x, _ in prices}) != len(prices):
        raise ValueError('test ratios must be strictly increasing')
    cells, missing = envelope(n, windows, block, budgets, left, right)
    if not cells or missing:
        raise ValueError('the schedule leaves a ratio uncovered')
    violations, probes = separate(n, windows, block, prices)
    if violations or sum(budgets) != sum(w for _, w in prices):
        raise ValueError('failed unrestricted lower certificate')
    return len(cells), probes


def verify_cost_ranges(n, windows, block, prices):
    """Independently test the dual using integer square roots and recursive budget intervals."""
    points = [x for x, _ in prices]
    prefix = [0]
    for _, weight in prices:
        prefix.append(prefix[-1]+weight)
    tests = 0
    for window in windows:
        pivot = bisect_left(points, Fraction(window[0], window[1]))
        # On each side the first block covering a ratio increases with distance
        # from a/b. Divide the budget interval until its highest possible price
        # fits its smallest budget. All larger budgets trivially cover at most
        # total_price, so [0,total_price) suffices.
        stack = [(0, prefix[-1]-1)]
        known = {}
        while stack:
            low, high = stack.pop()
            if low > high:
                continue
            if high not in known:
                left, right = 0, pivot
                while left < right:
                    mid = (left+right)//2
                    if cover_cost(n, window, block, points[mid]) <= high:
                        right = mid
                    else:
                        left = mid+1
                start = left
                left, right = pivot, len(points)
                while left < right:
                    mid = (left+right)//2
                    if cover_cost(n, window, block, points[mid]) <= high:
                        left = mid+1
                    else:
                        right = mid
                known[high] = prefix[left]-prefix[start]
                tests += 1
            price = known[high]
            if price > high:
                raise ValueError('weighted test ratios violate a budget')
            if price > low:
                mid = (low+high)//2
                stack.extend(((low, mid), (mid+1, high)))
    return tests


def solve(n, k, block, *, slack=4, max_centers=32768, max_points=180000,
          max_columns=500000, max_rounds=200, verbose=False):
    if n < 2 or block < 1 or k < 1 or slack < 0:
        raise ValueError('positive input, slope order and block size required')
    left, right = Fraction(1), Fraction(2)
    slopes = bounded_slopes(k, max_centers)
    windows = [(a, b, *lattice_start(n, a, b, 24)) for a, b in slopes]
    chosen, _, cuts, lengths = fast(n, k, block, max_centers=max_centers)
    initial = {s: (length+block-1)//block for s, length in zip(chosen, lengths)}
    caps = [slack+initial.get(s, 0) for s in slopes]
    points = {Fraction(*p) for p in slopes+cuts}
    stats = dict(rounds=0, peak_columns=0, cap_expansions=0, separation_probes=0,
                 initial_cost=sum(initial.values()))
    for iteration in range(1, max_rounds+1):
        if len(points) > max_points:
            raise ValueError('test-ratio budget exhausted')
        budgets, prices, columns = restricted_cover(n, windows, block, sorted(points), caps, max_columns)
        cells, missing = envelope(n, windows, block, budgets, left, right)
        stats.update(rounds=iteration, peak_columns=max(stats['peak_columns'], columns))
        if verbose:
            print('round', iteration, 'points', len(points), 'columns', columns,
                  'cost', sum(budgets), 'holes', len(missing), file=sys.stderr, flush=True)
        if missing:
            if missing & points:
                raise ArithmeticError('a previously covered ratio became uncovered')
            points.update(missing)
            continue
        violations, probes = separate(n, windows, block, prices)
        stats['separation_probes'] += probes
        if not violations:
            if sum(budgets) != sum(weight for _, weight in prices):
                raise ArithmeticError('primal and unrestricted dual do not match')
            stats.update(points=len(points), final_columns=columns, active_segments=len(cells),
                         priced_ratios=len(prices))
            return dict(windows=windows, budgets=budgets, prices=prices, cells=cells,
                        optimum=sum(budgets), stats=stats)
        for index, budget in violations:
            if budget <= caps[index]:
                raise ArithmeticError('dual violates an existing column')
            caps[index] = 2*budget+1
        stats['cap_expansions'] += len(violations)
        if verbose:
            print('expanding', len(violations), 'local caps; largest violated cost',
                  max(g for _, g in violations), file=sys.stderr, flush=True)
    raise ValueError('cut and column round budget exhausted')


def compact(n, k, block, result):
    """Keep only the public parameters and the primal and dual witnesses."""
    return dict(format='farey-trace-cover-v1', stride=24, ratio_interval=[1, 2],
                n=str(n), k=k, block=block, optimum=result['optimum'],
                budgets=[[i, g] for i, g in enumerate(result['budgets']) if g],
                prices=[[x.numerator, x.denominator, w] for x, w in result['prices']])


def read_certificate(path, n, k, block):
    data = json.loads(path.read_text())
    if (data.get('format'), data.get('stride'), data.get('ratio_interval')) != ('farey-trace-cover-v1', 24, [1, 2]):
        raise ValueError('unexpected certificate model')
    if (data['n'], data['k'], data['block']) != (str(n), k, block):
        raise ValueError('certificate parameters differ from the public comparison')
    slopes = bounded_slopes(k, 32768)
    windows = [(a, b, *lattice_start(n, a, b, 24)) for a, b in slopes]
    budgets = [0]*len(windows)
    for i, g in data['budgets']:
        if type(i) is not int or not 0 <= i < len(windows) or budgets[i] or type(g) is not int or g < 1:
            raise ValueError('invalid or repeated nonzero slope budget')
        budgets[i] = g
    if type(data['optimum']) is not int or sum(budgets) != data['optimum']:
        raise ValueError('reported optimum differs from total allocated budget')
    prices = []
    for numerator, denominator, weight in data['prices']:
        if type(numerator) is not int or type(denominator) is not int or denominator < 1:
            raise ValueError('invalid test ratio in certificate')
        prices.append((Fraction(numerator, denominator), weight))
    return dict(windows=windows, budgets=budgets, prices=prices, optimum=data['optimum'])


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--case', type=int, choices=range(4),
                        help='0=63, 1=79, 2=89-A, 3=89-B from farey-allocation.json')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--certificate', type=Path, help='save a reproducible compact optimum witness')
    mode.add_argument('--verify', type=Path, help='replay a saved certificate without optimization')
    parser.add_argument('--factor', action='store_true', help='also execute the priced collision search')
    parser.add_argument('--check-costs', action='store_true',
                        help='also check every dual inequality by independent cost bisection')
    parser.add_argument('--verbose', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    cases = json.loads((root/'research/farey-allocation.json').read_text())['cases']
    if args.verify and args.case is None:
        witness = json.loads(args.verify.read_text())
        matching = [row for row in cases if (row['n'], row['k'], row['baby_steps'])
                    == (witness['n'], witness['k'], witness['block'])]
        if len(matching) != 1:
            parser.error('certificate does not identify a unique public comparison')
        case = matching[0]
    else:
        case = cases[1 if args.case is None else args.case]
    n, k, block = int(case['n']), case['k'], case['baby_steps']
    summary = dict(case=case['id'], n=str(n), k=k, baby_steps=block)
    if args.verify:
        result = read_certificate(args.verify, n, k, block)
    else:
        start = perf_counter()
        result = solve(n, k, block, verbose=args.verbose)
        summary.update(solve_seconds=perf_counter()-start, stats=result['stats'])
    start = perf_counter()
    segments, probes = verify_sparse(n, result['windows'], block, Fraction(1), Fraction(2),
                                     result['budgets'], result['prices'])
    summary.update(verify_seconds=perf_counter()-start, verification_probes=probes,
                   segments=segments, optimum=result['optimum'], catalogue=len(result['windows']),
                   priced_ratios=len(result['prices']))
    if args.check_costs:
        start = perf_counter()
        tests = verify_cost_ranges(n, result['windows'], block, result['prices'])
        summary.update(independent_ranges=tests, independent_seconds=perf_counter()-start)
    if args.certificate:
        args.certificate.write_text(json.dumps(compact(n, k, block, result), separators=(',', ':'))+'\n')
    if args.factor:
        if 'cells' not in result:
            result['cells'], _ = envelope(n, result['windows'], block, result['budgets'], Fraction(1), Fraction(2))
        start = perf_counter()
        run = run_allocation(n, block, result)
        summary['collision_seconds'] = perf_counter()-start
        factor = run['factor']
        if factor is not None and (not 1 < factor < n or n % factor):
            raise ArithmeticError('collision search returned an invalid divisor')
        summary.update(factor=str(factor) if factor else None, cofactor=str(n//factor) if factor else None,
                       outcome=run['outcome'], schedule_complete=run['schedule_complete'], work=run['work'])
    try:
        from resource import RUSAGE_SELF, getrusage
        scale = 1024**2 if sys.platform == 'darwin' else 1024
        summary['peak_rss_mib'] = round(getrusage(RUSAGE_SELF).ru_maxrss/scale, 2)
    except ImportError:
        pass
    print(json.dumps(summary))


if __name__ == '__main__':
    main()
