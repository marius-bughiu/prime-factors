"""Collect smooth modular fractions of every balance along a Euclidean chain."""

import argparse
import json
from math import gcd
import platform
from time import process_time

from .pell_relations import check_rows
from .rational_squares import PANEL_BOUND, PANEL_BUDGET, PANEL_COUNT, PANEL_SEED
from .rational_squares import draw_root, factor_base, smooth, test_new_row
from .rational_squares import search as balanced_search


def euclidean_pairs(n, residue):
    """Yield (step, signed numerator, positive denominator) before the zero remainder."""
    old_b, b = n, residue
    old_a, a = 0, 1
    step = 0
    while b:
        yield step, b if a > 0 else -b, abs(a)
        q, rem = divmod(old_b, b)
        old_b, b = b, rem
        old_a, a = a, old_a - q*a
        step += 1


def search(n, mode, draws, bound, *, online=False, root_at=draw_root):
    """Keep the first or every primitive smooth fraction with twice its height below N."""
    if n <= 2 or n % 2 == 0 or mode not in ('first', 'all') or draws < 0 or bound < 2:
        raise ValueError('expected odd n > 2, first/all, nonnegative budget and bound >= 2')
    primes, base = factor_base(bound)
    work = dict(factor=None, outcome='no_split', draws=0, random_words=0, candidates=0,
                euclidean_states=0, accepted_draws=0, smooth_rows=0, private_pruned=0,
                pruning_rounds=0, min_private_bits=None, dependencies=0, tested=0, selected_steps=[])
    rows = []
    pivots = {}
    for i in range(draws):
        x, words = root_at(n, i)
        if not 0 < x < n:
            raise ValueError('sample must lie strictly between zero and the modulus')
        work['random_words'] += words
        work['draws'] += 1
        d = gcd(x, n)
        if d > 1:
            return dict(work, factor=d, outcome='sample_gcd')
        accepted = False
        for step, b, a in euclidean_pairs(n, x*x % n):
            work['euclidean_states'] += 1
            norm = b*a
            if 2*abs(norm) >= n:
                continue
            work['candidates'] += 1
            if not smooth(abs(norm), base):
                continue
            d = gcd(a, n)
            if d > 1:
                return dict(work, factor=d, outcome='denominator_gcd')
            root = (a*x) % n
            if gcd(a, abs(b)) != 1 or (root*root - norm) % n:
                raise ArithmeticError('invalid reduced modular fraction')
            if not accepted:
                work['accepted_draws'] += 1
                accepted = True
            work['smooth_rows'] += 1
            rows.append(([i+1, step], norm, root))
            if online and test_new_row(n, rows, pivots, primes, work):
                return work
            if mode == 'first':
                break
    return work if online else check_rows(n, rows, work)


def compare_panel(first_long):
    from .crt_holdout import draw_sample
    count = 1 if first_long else PANEL_COUNT
    budget = 2**21 if first_long else PANEL_BUDGET
    cases = []
    for attempt, n, expected in draw_sample(PANEL_SEED, count):
        methods = {}
        modes = ('balanced', 'first', 'all') if first_long else ('first', 'all')
        for mode in modes:
            start = process_time()
            if mode == 'balanced':
                work = balanced_search(n, 'fraction', budget, PANEL_BOUND, online=True)
            else:
                work = search(n, mode, budget, PANEL_BOUND, online=first_long)
            elapsed = process_time() - start
            d = work.pop('factor')
            factors = [] if d is None else sorted((d, n//d))
            if factors and (n % d or factors != expected):
                raise ArithmeticError('incorrect factorization in chain experiment')
            methods[mode] = dict(factors=list(map(str, factors)), remaining=[] if factors else [str(n)],
                                 work=work, cpu_seconds=round(elapsed, 4))
        cases.append(dict(attempt=attempt, n=str(n), expected_factors=list(map(str, expected)), methods=methods))
    return dict(seed=PANEL_SEED.decode(), count=count, draws=budget, bound=PANEL_BOUND, online=first_long,
                python=platform.python_version(), platform=platform.platform(), cases=cases)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?')
    parser.add_argument('--mode', choices=('first', 'all'), default='all')
    parser.add_argument('--draws', type=int, default=8192)
    parser.add_argument('--bound', type=int, default=4096)
    parser.add_argument('--online', action='store_true')
    parser.add_argument('--panel', action='store_true')
    parser.add_argument('--first-long', action='store_true')
    args = parser.parse_args()
    if args.panel or args.first_long:
        print(json.dumps(compare_panel(args.first_long), indent=2))
    elif args.n is not None:
        print(json.dumps(search(args.n, args.mode, args.draws, args.bound, online=args.online)))
    else:
        parser.error('supply an odd product or --panel')
