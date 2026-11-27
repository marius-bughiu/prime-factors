"""Exhaust every ordered-by-size pair of distinct 16-bit primes in the fixed product bin."""
from bisect import bisect_left, bisect_right
from collections import Counter
from functools import lru_cache
import json
from math import gcd, isqrt

from .gap_coverage import primes_through
from .shared_multiplier_selection import probe


@lru_cache(maxsize=None)
def offsets(a, b, residue, start, count):
    allowed = gcd(a+b*residue, 24)
    period = [i for i in range(24) if gcd(start+i, 24) == allowed]
    return tuple(24*(i//len(period))+period[i%len(period)] for i in range(count))


def labels(n, a, b, count):
    start = 1+isqrt(4*a*b*n-1)
    return [start+i for i in offsets(a, b, n%24, start%24, count)]


def search(n):
    """All three schedules share the ordinary prefix. Input contains only N."""
    ordinals = labels(n, 1, 1, 33)
    six = labels(n, 3, 2, 16)
    other = labels(n, 7, 5, 8)
    first, _ = probe(n, 1, ordinals[:16])
    ordinary, _ = probe(n, 1, ordinals[16:])
    six_start, _ = probe(n, 6, six[:7])
    six_end, _ = probe(n, 6, six[7:])
    thirtyfive, _ = probe(n, 35, other)
    return first, ordinary, six_start|six_end, six_start|thirtyfive


def population():
    limit = 1 << 16
    primes = [p for p in primes_through(limit-1) if p >= limit//2]
    total = common = 0
    outcomes = Counter()
    for i, p in enumerate(primes):
        lo = max(i+1, bisect_left(primes, (9*limit**2+16*p-1)//(16*p)))
        hi = bisect_right(primes, 5*limit**2//(8*p))
        for q in primes[lo:hi]:
            total += 1
            prefix, ordinary, switched, joint = search(p*q)
            if any(f != p for f in prefix|ordinary|switched|joint):
                raise ValueError('gcd disagrees with trial-sieved factors')
            if prefix:
                common += 1
            else:
                outcomes[(bool(ordinary), bool(switched), bool(joint))] += 1
    arms = ('ordinary', 'six', 'six_and_thirtyfive')
    extra = {arm: sum(v for flags, v in outcomes.items() if flags[i]) for i, arm in enumerate(arms)}
    return dict(prime_bits=16, products=total, common_prefix_splits=common,
                additional_splits=extra, total_splits={k: common+v for k, v in extra.items()},
                unresolved={k: total-common-v for k, v in extra.items()},
                extra_outcomes={'/'.join(str(int(b)) for b in flags): v for flags, v in sorted(outcomes.items())})


if __name__ == '__main__':
    print(json.dumps(population(), indent=2))
