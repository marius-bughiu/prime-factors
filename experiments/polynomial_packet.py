"""Find all small reduced norms at one coefficient across all quadratic-sieve roots."""
import argparse
import json
from math import gcd, isqrt, prod

from .gap_coverage import primes_through
from .phase_interval import approximate_slope


def example_coefficient():
    """Public coefficient shared by the positive and crossed comparison products."""
    g = (1 << 260) * prod(primes_through(173)[1:])
    return g * g


def search(n, coefficient, height, max_lifts=1):
    """Search nonnegative roots m over all residue classes at one coefficient."""
    if n < 3 or coefficient < 1 or height < 0 or max_lifts < 0:
        raise ValueError('expected a positive coefficient and nonnegative search bounds')
    ah = coefficient * height
    lower_square = max(0, n - ah)
    low = isqrt(lower_square)
    low += low * low < lower_square
    high = isqrt(n + ah)
    if low > high:
        return dict(factor=None, interval_complete=True, radius="0", euclidean_steps=0,
                    possible_lifts="0", tested_lifts=0, rows=[], square_norms=0)
    center = (low + high) // 2
    radius = high - center
    multiplier, slope, steps = approximate_slope(2 * center, coefficient, max(1, 4 * radius))
    constant = multiplier * (center * center - n) % coefficient
    error = multiplier * radius**2 + abs(slope) * radius
    first = -((error - constant) // coefficient)
    last = (error + constant) // coefficient
    possible = max(0, last - first + 1)
    tested = min(max_lifts, possible)
    rows = set()
    for lift in range(first, first + tested):
        disc = slope * slope - 4 * multiplier * (constant - lift * coefficient)
        if disc < 0:
            continue
        root = isqrt(disc)
        if root * root != disc:
            continue
        for numerator in (-slope - root, -slope + root):
            x, rem = divmod(numerator, 2 * multiplier)
            m = center + x
            if rem or not low <= m <= high:
                continue
            q, rem = divmod(m * m - n, coefficient)
            if not rem and abs(q) <= height:
                rows.add((m, q))
    factor = None
    square_norms = 0
    for m, q in sorted(rows):
        difference = coefficient * q
        if difference < 0:
            continue
        v = isqrt(difference)
        if v * v == difference:
            square_norms += 1
            d = gcd(m - v, n)
            if 1 < d < n:
                factor = min(d, n // d)
    return dict(factor=factor, interval_complete=(tested == possible),
                radius=str(radius), euclidean_steps=steps, possible_lifts=str(possible),
                tested_lifts=tested, rows=[[str(m), str(q)] for m, q in sorted(rows)],
                square_norms=square_norms)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--coefficient', type=int, default=example_coefficient())
    parser.add_argument('--height', type=int, default=1 << 308)
    parser.add_argument('--max-lifts', type=int, default=1)
    args = parser.parse_args()
    print(json.dumps(search(args.n, args.coefficient, args.height, args.max_lifts)))
