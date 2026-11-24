"""Exhaustively compare primitive short fractions from one square residue on small semiprimes."""

import argparse
from collections import Counter, defaultdict
from itertools import combinations
import json
from math import gcd, isqrt, prod

from .fraction_chains import euclidean_pairs
from .gap_coverage import primes_through


def direct_fractions(n, residues):
    """Index all reduced b/a with unit a, square residue and 0 < 2*a*abs(b) < n."""
    fractions = defaultdict(set)
    limit = (n - 1) // 2
    for a in range(1, limit + 1):
        if gcd(a, n) != 1:
            continue
        inverse = pow(a, -1, n)
        for b in range(1, limit // a + 1):
            if gcd(a, b) != 1:
                continue
            positive = b * inverse % n
            if positive in residues:
                fractions[positive].add((b, a))
            if n - positive in residues:
                fractions[n - positive].add((-b, a))
    return fractions


def short_fractions(n, residue):
    return [(b, a) for _, b, a in euclidean_pairs(n, residue)
            if 2 * a * abs(b) < n and gcd(a, b) == 1]


def pair_witness(n, residue, left, right):
    """Verify the mixed ratio and both original gcds of two distinct reduced short fractions."""
    b, a = left
    d, c = right
    signed_product = (a * b) * (c * d)
    if signed_product <= 0:
        return None
    root = isqrt(signed_product)
    if root * root != signed_product:
        return None
    cross_left, cross_right = a * abs(d), c * abs(b)
    common = gcd(cross_left, cross_right)
    u, v = isqrt(cross_left // common), isqrt(cross_right // common)
    if (common * u*u, common * v*v) != (cross_left, cross_right) or gcd(u, v) != 1:
        raise ArithmeticError('the two reduced cross products were not coprime squares')
    ratio = u * pow(v, -1, n) % n
    if u == v or 2*u*v >= n or ratio*ratio % n != 1 or ratio in (1, n-1):
        raise ArithmeticError('short overlapping fractions failed to give a mixed root')
    numerator = a * c * residue % n
    factors = sorted((gcd(numerator - root, n), gcd(numerator + root, n)))
    if factors[0] <= 1 or prod(factors) != n:
        raise ArithmeticError('the square dependency failed to split the semiprime')
    return dict(reduced_ratio=[u, v], mixed_root=ratio, left_root=numerator,
                right_root=root, factors=factors)


def minimal_dependencies(n, rows, roots, length):
    """Classify subsets with square product and no proper nonempty square subproduct."""
    totals = Counter()
    for selected in combinations(rows, length):
        norms = [a*b for b, a in selected]
        value = prod(norms)
        if value <= 0 or isqrt(value)**2 != value:
            continue
        proper = (prod(part) for count in range(1, length) for part in combinations(norms, count))
        if any(t > 0 and isqrt(t)**2 == t for t in proper):
            continue
        denominators = prod(a for _, a in selected)
        y = isqrt(value)
        successes = sum(1 < gcd(denominators * pow(x, length, n) - y, n) < n for x in roots)
        totals[f'minimal_{length}_rows_splitting_{successes}_roots'] += 1
    return totals


def census_product(p, q, *, extended=False):
    """Use the known primes only as labels and to verify exhaustive root counts."""
    n = p*q
    roots = defaultdict(list)
    for x in range(1, n):
        if gcd(x, n) == 1:
            roots[x*x % n].append(x)
    if len(roots) != (p-1)*(q-1)//4 or any(len(xs) != 4 for xs in roots.values()):
        raise ValueError('expected two distinct odd primes')
    direct = direct_fractions(n, roots)
    mixed = set(roots[1]) - {1, n-1}
    # The earlier Euclidean row has the smaller denominator and larger absolute
    # numerator. Its reduced ratio u/v is therefore always less than one.
    allowed = {(u, v) for w in mixed for u, v in short_fractions(n, w) if 0 < u < v}
    realized = set()
    counts = Counter(products=1, square_residues=len(roots), mixed_chain_ratios=len(allowed),
                     short_fractions=0, pairs_tested=0, square_pairs=0, successful_residues=0)
    for residue, xs in roots.items():
        rows = short_fractions(n, residue)
        if len(rows) != len(direct[residue]) or set(rows) != direct[residue]:
            raise ArithmeticError('Euclidean chain disagrees with direct fraction enumeration')
        counts['short_fractions'] += len(rows)
        success = False
        for left, right in combinations(rows, 2):
            counts['pairs_tested'] += 1
            witness = pair_witness(n, residue, left, right)
            if witness is None:
                continue
            ratio = tuple(witness['reduced_ratio'])
            if ratio not in allowed or witness['factors'] != [p, q]:
                raise ArithmeticError('mixed-root chain or exact factors disagree')
            realized.add(ratio)
            counts['square_pairs'] += 1
            success = True
        counts['successful_residues'] += int(success)
        if extended:
            for length in (3, 4):
                counts.update(minimal_dependencies(n, rows, xs, length))
    counts['realized_ratios'] = len(realized)
    return counts


def census(prime_limit, *, extended=False):
    """Group every p<q≤prime_limit of equal bit length by that common length."""
    grouped = defaultdict(Counter)
    primes = [p for p in primes_through(prime_limit) if p > 2]
    for p, q in combinations(primes, 2):
        if p.bit_length() == q.bit_length():
            grouped[p.bit_length()].update(census_product(p, q, extended=extended))
    total = Counter()
    for group in grouped.values():
        total.update(group)
    return dict(prime_limit=prime_limit, by_prime_bits=grouped, total=total)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prime-limit', type=int, default=127)
    parser.add_argument('--extended', action='store_true', help='also check every minimal 3- and 4-row dependency')
    args = parser.parse_args()
    print(json.dumps(census(args.prime_limit, extended=args.extended), sort_keys=True, indent=2))
