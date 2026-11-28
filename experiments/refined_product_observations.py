"""Compare the best single sum guess from coarse and refined product residues."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt


def compare(modulus, refinement):
    """Use labeled uniform unit pairs at the fine modulus for both predictors."""
    if modulus < 1 or refinement < 1 or refinement % modulus:
        raise ValueError('The fine modulus must be a positive multiple of the coarse modulus')
    units = [a for a in range(refinement) if gcd(a, refinement) == 1]
    coarse = defaultdict(Counter)
    fine = defaultdict(Counter)
    for a in units:
        for b in units:
            n = a * b % refinement
            s = (a + b) % modulus
            coarse[n % modulus][s] += 1
            fine[n][s] += 1
    for n, weights in fine.items():
        parent = coarse[n % modulus]
        if weights.keys() != parent.keys():
            raise AssertionError('Refinement changed the attained sums')
        parent_mass, fine_mass = sum(parent.values()), sum(weights.values())
        if any(w * parent_mass != parent[s] * fine_mass for s, w in weights.items()):
            raise AssertionError('Refinement changed conditional sum frequencies')
    total = len(units) ** 2
    return tuple(Fraction(sum(max(weights.values()) for weights in rows.values()), total)
                 for rows in (coarse, fine))


def small_prime_bands(width, modulus, refinement, extra_high):
    """Fit each single-guess table to every eligible small prime pair."""
    lo = 1 << (width - 1)
    primes = [p for p in range(lo, 2 * lo)
              if all(p % i for i in range(2, isqrt(p) + 1))]
    groups = [defaultdict(Counter) for _ in range(3)]
    total = 0
    for p, q in combinations(primes, 2):
        n = p * q
        if n.bit_length() != 2 * width:
            continue
        total += 1
        fine = n % refinement
        prefix = n >> (2 * width - 1 - extra_high)
        for group, key in zip(groups, (n % modulus, fine, (fine, prefix))):
            group[key][(p + q) % modulus] += 1
    return total, tuple(sum(max(row.values()) for row in group.values()) for group in groups)


if __name__ == '__main__':
    for m, d in ((25, 400), (25, 125), (175, 700)):
        coarse, fine = compare(m, d)
        print(f'Sum modulo {m}, product refined to {d}: best one-guess rate {coarse} -> {fine}')
    total, hits = small_prime_bands(10, 25, 400, 3)
    print(f'All {total} full-width products of distinct ten-bit primes: '
          f'best one-guess hits for coarse, refined and refined plus prefix = {hits}')
