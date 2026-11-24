"""Find every two-row square dependency on a short-fraction chain without factoring its rows."""

import argparse
from collections import defaultdict
from functools import lru_cache
import json
from math import gcd, isqrt

from .fraction_chains import euclidean_pairs
from .rational_squares import draw_root


@lru_cache(maxsize=1)
def sign_tables():
    primes = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53)
    return tuple((p, frozenset(x*x % p for x in range(1, (p + 1) // 2))) for p in primes)


def square_class_key(value):
    """Group candidates by sign, valuation parity and the square class of each unit part."""
    if value == 0:
        raise ValueError('expected a nonzero signed norm')
    key = int(value < 0)
    magnitude = abs(value)
    for p, squares in sign_tables():
        unit = magnitude
        residue = unit % p
        parity = 0
        while residue == 0:
            unit //= p
            parity ^= 1
            residue = unit % p
        key = (key << 2) | (parity << 1) | int(residue in squares)
    return key


def square_product_root(first, second):
    """Return the exact positive square root of the product, or None."""
    if not first or not second or (first < 0) != (second < 0):
        return None
    left, right = abs(first), abs(second)
    shared = gcd(left, right)
    left //= shared
    right //= shared
    u, v = isqrt(left), isqrt(right)
    if u*u != left or v*v != right:
        return None
    return shared*u*v


def check_source(n, residue, work):
    """Inspect a chain of one unit, which can itself be a square or a nonsquare."""
    buckets = defaultdict(list)
    seen = 0
    for step, b, a in euclidean_pairs(n, residue):
        work['euclidean_states'] += 1
        norm = a*b
        if 2*abs(norm) >= n:
            continue
        common = gcd(a, abs(b))
        if common > 1:
            if n % common:
                raise ArithmeticError('nonprimitive Euclidean vector has an invalid divisor')
            work.update(factor=common, outcome='coefficient_gcd')
            return True
        work['short_fractions'] += 1
        # Count every earlier row, including those whose keys rule out an exact test.
        work['possible_pairs'] += seen
        seen += 1
        group = buckets[square_class_key(norm)]
        for old_step, old_b, old_a in group:
            work['exact_pair_tests'] += 1
            right = square_product_root(old_a*old_b, norm)
            if right is None:
                continue
            left = old_a*a*residue % n
            if (left*left-right*right) % n:
                raise ArithmeticError('invalid congruence from the two fractions')
            factor = gcd(left-right, n)
            if not 1 < factor < n:
                raise ArithmeticError('distinct primitive short fractions gave only a global sign')
            work.update(factor=factor, outcome='pair', source_residue=str(residue),
                        fractions=[[old_step, str(old_b), str(old_a)], [step, str(b), str(a)]])
            return True
        group.append((step, b, a))
    return False


def search(n, mode, draws):
    if n <= 2 or n % 2 == 0 or mode not in ('unit', 'square') or draws < 0:
        raise ValueError('expected odd n > 2, unit/square, and a nonnegative draw limit')
    work = dict(factor=None, outcome='no_split', draws=0, random_words=0, euclidean_states=0,
                short_fractions=0, possible_pairs=0, exact_pair_tests=0, source_residue=None, fractions=[])
    for i in range(draws):
        x, words = draw_root(n, i)
        work['draws'] += 1
        work['random_words'] += words
        d = gcd(x, n)
        if d > 1:
            return dict(work, factor=d, outcome='sample_gcd')
        residue = x if mode == 'unit' else x*x % n
        if check_source(n, residue, work):
            break
    return work


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--mode', choices=('unit', 'square'), default='unit')
    parser.add_argument('--draws', type=int, default=256)
    args = parser.parse_args()
    print(json.dumps(search(args.n, args.mode, args.draws)))
