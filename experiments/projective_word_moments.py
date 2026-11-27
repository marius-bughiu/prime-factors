"""Check fixed-line totals and Jacobi moments by enumeration at five small levels."""

import json
from itertools import product
from math import comb, gcd, isqrt
from pathlib import Path


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/projective-word-moments.json'


def jacobi(value, modulus):
    """Binary Jacobi algorithm for a positive odd modulus."""
    sign = 1
    while value % modulus:
        value %= modulus
        while value % 2 == 0:
            value //= 2
            if modulus % 8 in (3, 5):
                sign = -sign
        if value % 4 == modulus % 4 == 3:
            sign = -sign
        value, modulus = modulus, value
    return sign if modulus == 1 else 0


def projective_points(n):
    """Group primitive coordinates modulo multiplication by a unit."""
    units = [u for u in range(n) if gcd(u, n) == 1]
    representatives = []
    orbit = {}
    for x, y in product(range(n), repeat=2):
        if gcd(x, y, n) != 1 or (x, y) in orbit:
            continue
        label = len(representatives)
        representatives.append((x, y))
        for u in units:
            orbit[u*x % n, u*y % n] = label
    return representatives, orbit


def measure(n):
    if n < 3 or n > 221 or n % 2 == 0:
        raise ValueError('The direct projective-coordinate comparison supports odd toy levels 3–221')
    points, orbit = projective_points(n)
    fixed_total = sum(orbit[(t*x-y) % n, x] == index
                      for t in range(n) for index, (x, y) in enumerate(points))
    signs = [jacobi(t*t-4, n) for t in range(n)]
    powers = [1] * n
    for k in range(isqrt(n) + 1):
        observed = sum(power*sign for power, sign in zip(powers, signs)) % n
        predicted = (comb(k, k//2) if k % 2 == 0 else 0) % n
        if observed != predicted:
            return dict(level=n, points=len(points), point_tests=n*len(points), fixed_sum=fixed_total,
                        sign_sum=sum(signs), zeros=signs.count(0), degree=k, observed=observed,
                        predicted=predicted, jacobi_terms=n, moment_terms=n*(k+1),
                        boundary_divisor=gcd(observed-predicted, n))
        powers = [(t*power) % n for t, power in enumerate(powers)]
    raise ValueError(f'No exceptional degree through {isqrt(n)} for level {n}')


def check_case(case):
    n = int(case['n'])
    result = measure(n)
    # The expected factors enter only after the measurement.
    p, q = map(int, case['factors'])
    assert n == p*q and 2 < p < q
    assert result['fixed_sum'] == (p-1)*(q-1)
    assert result['sign_sum'] == 1
    assert result['zeros'] == 2*(p+q)-4
    assert result['degree'] == p-1
    difference = result['observed'] - result['predicted']
    assert difference % p == 1 and difference % q == 0
    assert result['boundary_divisor'] == q
    return result


def main():
    for case in json.loads(FIXTURE.read_text()):
        result = check_case(case)
        print(' '.join(f'{key}={value}' for key, value in result.items()))

    # Equality at a later even degree rules out a monotone even-degree test.
    for n, k, expected in ((15, 10, 12), (77, 60, 0)):
        observed = sum(pow(t, k, n) * jacobi(t*t-4, n) for t in range(n)) % n
        assert observed == comb(k, k//2) % n == expected


if __name__ == '__main__':
    main()
