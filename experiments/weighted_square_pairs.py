"""Compare two public weighted square excesses and matched extra square tests.

Run python3 -m experiments.weighted_square_pairs to replay the complete small census.
"""

import json
from itertools import combinations
from math import gcd, isqrt

from .gap_coverage import primes_through


def first_label(n, weight):
    stride = gcd(24, 2 * (weight + n))
    bottom = 1 + isqrt(4 * weight * n - 1)
    return bottom + (weight + n - bottom) % stride, stride


def row_factor(n, label, excess):
    root = isqrt(excess)
    if root * root == excess:
        divisor = gcd(n, label - root)
        if 1 < divisor < n:
            return divisor
    return None


def search(n):
    """Read just N. Compare the first admissible label at weights 1 and 2."""
    if n <= 1 or gcd(n, 6) != 1:
        raise ValueError('expected an integer greater than one and coprime to six')
    a, _ = first_label(n, 1)
    b, _ = first_label(n, 2)
    d, e = a*a - 4*n, b*b - 8*n
    root = isqrt(d*e)
    square = root*root == d*e
    divisor = gcd(n, a*b-root) if square else None
    factor = divisor if divisor is not None and 1 < divisor < n else None
    return dict(factor=factor, labels=[str(a), str(b)], excesses=[str(d), str(e)],
                square=square, root=str(root) if square else None,
                square_tests=1, label_roots=2, gcd_tests=int(square))


def census(bits):
    floor = 1 << (bits - 1)
    primes = [p for p in primes_through(2*floor-1) if p >= floor]
    counts = dict(eligible=0, either_first=0, cross=0, additional_cross=0,
                  next_first_only_gain=0, next_second_only_gain=0, cross_missed_by_both_next=0)
    first_extra = None
    for p, q in combinations(primes, 2):
        n = p*q
        if n < 2*floor*floor:
            continue
        a, sa = first_label(n, 1)
        b, sb = first_label(n, 2)
        d, e = a*a-4*n, b*b-8*n
        joint = isqrt(d*e)
        factor = gcd(n, a*b-joint) if joint*joint == d*e else 1
        shared = 1 < factor < n
        if shared and factor not in (p, q):
            raise ArithmeticError('square match gave an invalid divisor')
        single = bool(row_factor(n, a, d) or row_factor(n, b, e))
        counts['eligible'] += 1
        counts['either_first'] += int(single)
        counts['cross'] += int(shared)
        if not single:
            left = row_factor(n, a+sa, d+sa*(2*a+sa))
            right = row_factor(n, b+sb, e+sb*(2*b+sb))
            counts['additional_cross'] += int(shared)
            counts['next_first_only_gain'] += int(bool(left))
            counts['next_second_only_gain'] += int(bool(right))
            counts['cross_missed_by_both_next'] += int(shared and not (left or right))
            if shared and first_extra is None:
                first_extra = str(n)
    return dict(factor_bits=bits, **counts, first_additional_product=first_extra)


if __name__ == '__main__':
    print(json.dumps([census(bits) for bits in range(8, 17)], indent=2))
