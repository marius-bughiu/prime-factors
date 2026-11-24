"""Compare two ways of collecting smooth relations from the same modular squares."""

import argparse
from functools import lru_cache
from hashlib import shake_256
import json
from math import gcd, isqrt, prod
from pathlib import Path
import platform
from time import process_time

from .pell_relations import check_rows, dependency_gcd, insert_parity
from .gap_coverage import primes_through

PANEL_SEED = b'rational-square-panel-v1'
PANEL_COUNT = 16
PANEL_BUDGET = 8192
PANEL_BOUND = 4096
MODES = ('centered', 'fraction')


def reconstruct(n, residue, limit):
    """First Euclidean remainder at most limit, with its signed cofactor."""
    previous, remainder = n, residue
    old_cofactor, cofactor = 0, 1
    divisions = 0
    while remainder > limit:
        quotient, following = divmod(previous, remainder)
        previous, remainder = remainder, following
        old_cofactor, cofactor = cofactor, old_cofactor - quotient * cofactor
        divisions += 1
    numerator = remainder if cofactor > 0 else -remainder
    return numerator, abs(cofactor), divisions


def draw_root(n, serial):
    """Draw uniformly in [1,n) in the random-byte model, with a reproducible stream."""
    length = (n.bit_length() + 7) // 8
    prefix = b'rational-square-root-v1\0' + n.to_bytes(length, 'big') + serial.to_bytes(8, 'big')
    mask = (1 << (n-2).bit_length()) - 1
    trial = 0
    while True:
        raw = shake_256(prefix + trial.to_bytes(8, 'big')).digest(length)
        z = int.from_bytes(raw, 'big') & mask
        trial += 1
        if z < n-1:
            return z+1, trial


@lru_cache(maxsize=8)
def factor_base(bound):
    primes = tuple(primes_through(bound))
    return primes, prod(primes)


def smooth(value, base):
    if value <= 0:
        raise ValueError('smoothness requires a positive magnitude')
    while value > 1:
        shared = gcd(value, base)
        if shared == 1:
            return False
        value //= shared
    return True


def prime_parity(norm, primes):
    """Coordinate zero records the sign. Each other coordinate records one prime."""
    parity, value = int(norm < 0), abs(norm)
    for i, p in enumerate(primes, 1):
        if value == 1:
            break
        while value % p == 0:
            parity ^= 1 << i
            value //= p
    if value != 1:
        raise ArithmeticError('row contains a prime outside the base')
    return parity


def test_new_row(n, rows, pivots, primes, work):
    """Test the new basis dependency, if any, formed by the last signed row."""
    _, norm, _ = rows[-1]
    mask = insert_parity(pivots, prime_parity(norm, primes), 1 << (len(rows)-1))
    if mask is None:
        return False
    work['dependencies'] += 1
    work['tested'] += 1
    divisor, chosen = dependency_gcd(n, rows, mask)
    if 1 < divisor < n:
        work.update(outcome='relation', factor=divisor, selected_steps=chosen)
        return True
    return False


def search(n, mode, draws, bound, *, online=False):
    """Check dependencies at the end of the budget, or immediately in online mode."""
    if n <= 2 or n % 2 == 0 or mode not in MODES or draws < 0 or bound < 2:
        raise ValueError('expected odd n > 2, a known mode, a nonnegative draw budget and bound >= 2')
    primes, base = factor_base(bound)
    limit = isqrt((n-1)//2)
    work = dict(factor=None, outcome='no_split', draws=0, random_words=0, euclidean_divisions=0,
                in_box=0, smooth_rows=0, private_pruned=0, pruning_rounds=0, min_private_bits=None,
                dependencies=0, tested=0, selected_steps=[])
    rows = []
    pivots = {}
    for i in range(draws):
        x, words = draw_root(n, i)
        work['draws'] += 1
        work['random_words'] += words
        divisor = gcd(x, n)
        if divisor > 1:
            return dict(work, factor=divisor, outcome='sample_gcd')
        residue = x*x % n
        if mode == 'fraction':
            numerator, denominator, divisions = reconstruct(n, residue, limit)
            work['euclidean_divisions'] += divisions
            divisor = gcd(denominator, n)
            if 1 < divisor < n:
                return dict(work, factor=divisor, outcome='denominator_gcd')
            if denominator > limit:
                continue
        else:
            numerator = residue if 2*residue < n else residue - n
            denominator = 1
        work['in_box'] += 1
        norm = numerator * denominator
        root = denominator*x % n
        if (root*root - norm) % n:
            raise ArithmeticError('incorrect square relation')
        if smooth(abs(norm), base):
            rows.append((i+1, norm, root))
            work['smooth_rows'] += 1
            if online and test_new_row(n, rows, pivots, primes, work):
                return work
    return work if online else check_rows(n, rows, work)


def compare_case(attempt, n, expected, budget, timed=False):
    methods = {}
    for mode in MODES:
        started = process_time()
        work = search(n, mode, budget, PANEL_BOUND)
        elapsed = process_time() - started
        divisor = work.pop('factor')
        factors = [] if divisor is None else sorted((divisor, n//divisor))
        if factors and (n % divisor or factors != expected):
            raise ArithmeticError('incorrect factorization in paired sample')
        methods[mode] = dict(factors=list(map(str, factors)), remaining=[] if factors else [str(n)], work=work)
        if timed:
            methods[mode]['cpu_seconds'] = round(elapsed, 4)
    return dict(attempt=attempt, n=str(n), expected_factors=list(map(str, expected)), methods=methods)


def run_panel(verify, first_long=False):
    from .crt_holdout import draw_sample, verify_cases
    count = 1 if first_long else PANEL_COUNT
    budget = 2**21 if first_long else PANEL_BUDGET
    cases = [compare_case(attempt, n, factors, budget, first_long)
             for attempt, n, factors in draw_sample(PANEL_SEED, count)]
    if verify:
        verify_cases(cases, Path(__file__).resolve().parents[1] / 'build' / 'rational-square-panel')
    if first_long:
        return dict(seed=PANEL_SEED.decode(), draws=budget, bound=PANEL_BOUND, python=platform.python_version(),
                    platform=platform.platform(), **cases[0])
    return dict(seed=PANEL_SEED.decode(), count=count, draws=budget, bound=PANEL_BOUND, cases=cases)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?')
    parser.add_argument('--mode', choices=MODES, default='fraction')
    parser.add_argument('--draws', type=int, default=PANEL_BUDGET)
    parser.add_argument('--bound', type=int, default=PANEL_BOUND)
    parser.add_argument('--panel', action='store_true')
    parser.add_argument('--first-long', action='store_true', help='repeat the first panel input at 2^21 draws')
    parser.add_argument('--online', action='store_true', help='test each dependency as it appears')
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    if args.panel or args.first_long:
        print(json.dumps(run_panel(args.verify, args.first_long), indent=2))
    elif args.n is not None:
        print(json.dumps(search(args.n, args.mode, args.draws, args.bound, online=args.online)))
    else:
        parser.error('supply an odd product or --panel')
