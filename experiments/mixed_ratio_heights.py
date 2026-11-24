"""Minimum fraction heights for a specified mixed root ratio; the primes label the small census."""

import argparse
from collections import Counter, defaultdict
from itertools import combinations
import json
from math import gcd, isqrt

from .gap_coverage import primes_through
from .same_source_pairs import short_fractions


def jacobi(a, n):
    """Jacobi symbol at an odd positive denominator."""
    if n <= 0 or n % 2 == 0:
        raise ValueError('expected a positive odd denominator')
    sign = 1
    a %= n
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        if a % 4 == n % 4 == 3:
            sign = -sign
        a, n = n % a, a
    return sign if n == 1 else 0


def least_nonresidue(n):
    return next(k for k in range(2, n) if jacobi(k, n) == -1)


def optimal_pair(p, q, u, v):
    """Construct the minimizing pair. u/v and the prime labels are supplied research inputs."""
    n = p*q
    w = u*v
    if not 0 < u < v or gcd(u, v) != 1 or gcd(w, n) != 1 or (u*u-v*v) % n:
        raise ValueError('expected a positive reduced mixed root ratio')
    if (u-v) % n == 0 or (u+v) % n == 0:
        raise ValueError('global sign cannot be a mixed root')
    if p % 4 == q % 4 == 3:
        d = next(k for k in range(w, 0, -1) if w*w % k == 0 and jacobi(k, n) == 1)
        ell = least_nonresidue(n)
        if ell*w < w*w//d:
            d, scale, height = w, ell, ell*w
        else:
            scale, height = 1, w*w//d
    else:
        d, scale, height = w, 1, w
    a, b = gcd(d, u*u), gcd(d, v*v)
    rows = [(scale*a, b), (scale*(v*v//b), u*u//a)]
    reduced = [(c//gcd(c, e), e//gcd(c, e)) for c, e in rows]
    residue = reduced[0][0] * pow(reduced[0][1], -1, n) % n
    # The prime labels are used here to exhibit the correct common sign in the census.
    if any(pow(residue, (k-1)//2, k) != 1 for k in (p, q)):
        residue = -residue % n
        reduced = [(-c, e) for c, e in reduced]
    assert all(pow(residue, (k-1)//2, k) == 1 for k in (p, q))
    assert all((c - e*residue) % n == 0 for c, e in reduced)
    (a, b), (c, e) = reduced
    assert a*e*v*v == c*b*u*u and max(abs(a)*b, abs(c)*e) == height
    return height, residue, reduced


def product_counts(p, q):
    n = p*q
    square_units = {x*x % n for x in range(1, n) if gcd(x, n) == 1}
    mixed = [x for x in range(2, n-1) if x*x % n == 1]
    ratios = {(u, v) for z in mixed for u, v in short_fractions(n, z) if 0 < u < v}
    predicted = {ratio: optimal_pair(p, q, *ratio)[0] for ratio in ratios}
    counts = Counter(products=1, mixed_ratios=len(ratios), square_eligible=0)
    cutoff = max(predicted.values(), default=0)
    # A constructed pair attains each proposed height. Enumerating all rows up to
    # the largest of those heights tests every possible smaller competitor.
    sign_allowed = square_units | {-x % n for x in square_units}
    positive_rows = defaultdict(list)
    for b in range(1, cutoff + 1):
        if gcd(b, n) != 1:
            continue
        inverse = pow(b, -1, n)
        for a in range(1, cutoff//b + 1):
            if gcd(a, b*n) == 1:
                r = a*inverse % n
                if r in sign_allowed:
                    positive_rows[r].append((a, b))
    observed = {}
    for rows in positive_rows.values():
        for (a, b), (c, e) in combinations(rows, 2):
            x, y = sorted((a*e, c*b))
            common = gcd(x, y)
            x, y = x//common, y//common
            u, v = isqrt(x), isqrt(y)
            if u*u != x or v*v != y or (u, v) not in ratios:
                continue
            height = max(a*b, c*e)
            observed[(u, v)] = min(height, observed.get((u, v), height))
    if observed != predicted:
        raise ArithmeticError('direct enumeration disagrees with the minimum height criterion')
    counts['square_eligible'] = sum(2*h < n for h in predicted.values())
    if p % 4 == q % 4 == 3:
        counts.update(blum_ratios=len(ratios), blum_eligible=counts['square_eligible'])
    return counts


def census(limit):
    counts = Counter()
    primes = [p for p in primes_through(limit) if p > 2]
    for p, q in combinations(primes, 2):
        if p.bit_length() == q.bit_length():
            counts.update(product_counts(p, q))
    return counts


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prime-limit', type=int, default=127)
    print(json.dumps(census(parser.parse_args().prime_limit), sort_keys=True))
