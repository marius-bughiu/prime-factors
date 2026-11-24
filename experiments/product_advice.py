"""Exact two-slot midpoint coverage with prefix and suffix advice in small prime boxes.

The table is optimized on the entire indicated population using its known pairs.
This measures the best possible table at that width, with unrestricted preprocessing.
"""

import argparse
from collections import Counter, defaultdict
from math import isqrt

if __package__:
    from .gap_coverage import primes_through
else:
    from gap_coverage import primes_through


def candidate_strides(d, distance, divisors):
    """All successful choices for a table allowed two reserved root slots."""
    if distance < 2:
        yield 1
    while d > 1:
        prime = divisors[d]
        power = 1
        while d % prime == 0:
            d //= prime
            power *= prime
            if (prime != 2 or power == 2) and distance < power * power:
                yield power


def coverage(bits, splits=None):
    if not 3 <= bits <= 15:
        raise ValueError('the exhaustive population supports 3 through 15 factor bits')
    x = 1 << (bits - 1)
    splits = sorted(set(splits if splits is not None else [0, (bits-1)//2, bits-1]))
    if any(k < 0 or k > bits - 1 for k in splits):
        raise ValueError('suffix must fit the advice budget')
    all_primes = primes_through(2*x)
    divisors = [1] * (x//2 + 1)
    for prime in all_primes:
        for v in range(prime, len(divisors), prime):
            divisors[v] = prime
    primes = [p for p in all_primes if p >= x]
    common = Counter()
    tables = {k: defaultdict(Counter) for k in splits}
    population = 0
    for i, p in enumerate(primes):
        for q in primes[i+1:]:
            n = p*q
            if n < 2*x*x:
                continue
            population += 1
            d = (q-p)//2
            distance = (p+q)//2 - isqrt(n-1) - 1
            choices = tuple(candidate_strides(d, distance, divisors))
            common.update(choices)
            for k, table in tables.items():
                # Exactly `bits` observed bits, including the known leading one.
                prefix = n >> (bits+k)
                suffix = n % (1 << k)
                table[prefix, suffix].update(choices)
    return dict(bits=bits, population=population,
                fixed=max(common.values(), default=0),
                with_advice={k: sum(max(row.values(), default=0) for row in table.values())
                             for k, table in tables.items()})


if __name__ == '__main__':
    from json import dumps
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bits', type=int, nargs='+')
    args = parser.parse_args()
    for bits in args.bits:
        print(dumps(coverage(bits)))
