"""Apply shared Jacobi sign tests to the whole balanced Fermat interval."""

from argparse import ArgumentParser
from json import dumps
from math import gcd, isqrt
from random import Random
from time import perf_counter


def reading(discriminant, seed):
    """Compute the sign after removing all denominator factors shared with 2D."""
    if discriminant < 1 or seed < 1:
        raise ValueError('the sign requires a positive discriminant and seed')
    modulus = seed
    common = gcd(modulus, 2*discriminant)
    while common > 1:
        modulus //= common
        common = gcd(modulus, 2*discriminant)
    value = discriminant % modulus
    sign = 1
    while value:
        while value % 2 == 0:
            value //= 2
            if modulus % 8 in (3, 5):
                sign = -sign
        if value % 4 == modulus % 4 == 3:
            sign = -sign
        value, modulus = modulus % value, value
    return sign


def balanced_midpoints(n):
    if n <= 1 or n % 2 == 0 or isqrt(n)**2 == n:
        raise ValueError('expected an odd nonsquare greater than one')
    first = isqrt(n) + 1
    first += ((n+1)//2 - first) % 2
    return range(first, isqrt(9*n//8) + 1, 2)


def search(n, tests, master_seed):
    if tests < 0:
        raise ValueError('the number of tests must be nonnegative')
    rng = Random(master_seed)
    seeds = [1+rng.getrandbits(2202) for _ in range(tests)]
    midpoints = balanced_midpoints(n)
    counts = [0] * (tests+1)
    pairs = []
    for h in midpoints:
        d = h*h-n
        counts[0] += 1
        for index, seed in enumerate(seeds, 1):
            if reading(d, seed) < 0:
                break
            counts[index] += 1
        else:
            gap = isqrt(d)
            if gap*gap == d and h-gap > 1:
                pairs.append((h-gap, h+gap))
    return dict(pairs=pairs, midpoints=counts[0], evaluations=sum(counts[:-1]),
                final_square_tests=counts[-1], survivors=counts, tests=tests)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--tests', type=int, default=16)
    parser.add_argument('--seed', type=int, default=1)
    parser.add_argument('--compare', action='store_true')
    args = parser.parse_args()
    for tests in ([0, args.tests] if args.compare else [args.tests]):
        start = perf_counter()
        result = search(args.n, tests, args.seed)
        print(dumps(dict(result, seconds=perf_counter()-start)))
