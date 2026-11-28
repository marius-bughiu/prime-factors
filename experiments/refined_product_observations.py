"""Compare the best single sum guess from coarse and refined product residues."""
from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd


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


if __name__ == '__main__':
    for m, d in ((25, 400), (25, 125), (175, 700)):
        coarse, fine = compare(m, d)
        print(f'Sum modulo {m}, product refined to {d}: best one-guess rate {coarse} -> {fine}')
