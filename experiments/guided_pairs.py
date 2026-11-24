"""Cover every two-fraction square with one short norm by scanning multiples of N."""

import argparse
from fractions import Fraction
import json
from math import gcd, isqrt


def cover(n, max_norm, max_multipliers=None):
    """Scan a superset of all qualifying pairs with one absolute norm at most max_norm."""
    if n < 3 or n % 2 == 0 or max_norm < 1:
        raise ValueError('expected an odd input above one and a positive norm limit')
    if max_multipliers is not None and max_multipliers < 0:
        raise ValueError('expected a nonnegative multiplier limit')
    # Both row norms are strictly below N/2.
    threshold = min(max_norm, (n - 1) // 2)
    last = (threshold - 1) // 2
    budget = last if max_multipliers is None else min(last, max_multipliers)
    work = dict(factor=None, outcome='no_split', multiplier_limit=last, multipliers=0,
                square_tests=0, multiplier=None, upper_root=None, gap_root=None)
    for h in range(1, budget + 1):
        work['multipliers'] += 1
        product = h*n
        largest_gap = (threshold - 1) // (2*h)
        upper = isqrt(product) + 1
        gap = upper*upper - product
        while gap <= largest_gap:
            work['square_tests'] += 1
            lower = isqrt(gap)
            if lower*lower == gap:
                divisor = gcd(upper - lower, n)
                if 1 < divisor < n:
                    return dict(work, factor=divisor, outcome='gap', multiplier=h,
                                upper_root=str(upper), gap_root=str(lower))
            gap += 2*upper + 1
            upper += 1
    if budget < last:
        work['outcome'] = 'budget_exhausted'
    return work


def anchor_from_roots(n, upper, lower, max_norm):
    """Reconstruct two primitive fractions from normalized roots and a bounded divisor.

    The divisor search is intentionally exhaustive for small examples. Its work grows
    with the supplied norm bound. An unsuccessful divisor search can follow a real split.
    """
    if n < 3 or max_norm < 1:
        raise ValueError('expected a modulus above two and a positive norm limit')
    if not (0 < lower < upper and (upper*upper - lower*lower) % n == 0 and
            gcd(upper, lower) == 1 and gcd(upper*lower, n) == 1):
        raise ValueError('expected coprime unit roots of equal squares modulo the input')
    product = (upper*lower)**2
    smallest = (2*product) // n + 1
    largest = min(max_norm, (n - 1) // 2)
    for norm in range(smallest, largest + 1):
        if product % norm:
            continue
        numerator = gcd(norm, upper*upper)
        denominator = norm // numerator
        other_num = lower*lower // denominator
        other_den = upper*upper // numerator
        return ((numerator, denominator), (other_num, other_den))
    return None


def input_probability_bound(norm_bits):
    """Rational upper bound for uniform admissible products at S = 2^norm_bits."""
    if norm_bits < 0 or norm_bits % 2 or norm_bits > 2044:
        raise ValueError('expected an even norm exponent from 0 to 2044')
    root = 2**(norm_bits // 2)
    # ln(2) < 0.7; sum_{j<=root} 1/j <= 1+ln(root).
    partners = 16 * root * (1 + Fraction(7*norm_bits, 20))
    # For X=2^1023, P<1.511 X/ln X and P_* - 1 >0.22 X/ln X.
    # There are at least P_*(P_*-1)/2 eligible unordered pairs; ln X < 710.
    return Fraction(2*1511*1000*710, 220**2) * partners / 2**1023


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--max-norm', type=int, default=65536)
    parser.add_argument('--max-multipliers', type=int)
    args = parser.parse_args()
    print(json.dumps(cover(args.n, args.max_norm, args.max_multipliers)))
