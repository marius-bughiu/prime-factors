"""Replay two sum orders on every distinct pair of 9-, 10- and 12-bit primes."""

import json
from dataclasses import asdict, dataclass
from itertools import combinations
from math import isqrt

from experiments.grouped_offset_sweep import is_prime


@dataclass
class Counts:
    earlier: int = 0
    tied: int = 0
    later: int = 0
    ascending_tests: int = 0
    prioritized_tests: int = 0
    priority_classifications: int = 0

    def record(self, ascending, prioritized, candidates):
        self.earlier += prioritized < ascending
        self.tied += prioritized == ascending
        self.later += prioritized > ascending
        self.ascending_tests += ascending
        self.prioritized_tests += prioritized
        self.priority_classifications += candidates


def first_square(n, sums):
    """One exact square root per visited sum, including the successful test."""
    for tests, s in enumerate(sums, start=1):
        diff = s*s - 4*n
        root = isqrt(diff)
        if root*root == diff:
            return tests, ((s-root)//2, (s+root)//2)
    raise AssertionError(f'no exact square for {n}')


def census():
    allowed = [set() for _ in range(25)]
    for a in range(25):
        for b in range(25):
            allowed[a*b % 25].add((a+b) % 25)
    unit_squares = {a*a % 25 for a in range(25) if a % 5}
    for bits in (9, 10, 12):
        lower_factor = 2**(bits-1)
        upper_factor = 2**bits - 1
        primes = [p for p in range(lower_factor, upper_factor+1) if is_prime(p)]
        groups = {name: Counts() for name in ('all', 'square', 'one')}
        for p, q in combinations(primes, 2):
            n = p*q
            lo = isqrt(4*n - 1) + 1
            hi = min(lower_factor+n//lower_factor, upper_factor+n//upper_factor)
            start = lo + (n+1-lo) % 4
            ascending = [s for s in range(start, hi+1, 4) if s % 25 in allowed[n % 25]]
            # Python sorting is stable, so each of the two groups stays ascending.
            prioritized = sorted(ascending, key=lambda s: (s*s-4*n) % 5 != 0)
            base, base_factors = first_square(n, ascending)
            cost, priority_factors = first_square(n, prioritized)
            assert base_factors == priority_factors == (p, q)
            groups['all'].record(base, cost, len(ascending))
            if n % 25 in unit_squares:
                groups['square'].record(base, cost, len(ascending))
            if n % 25 == 1:
                groups['one'].record(base, cost, len(ascending))
        yield {'bits': bits, 'primes': len(primes),
               'groups': {name: asdict(count) for name, count in groups.items()}}


if __name__ == '__main__':
    for result in census():
        print(json.dumps(result))
