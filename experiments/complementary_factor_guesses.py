"""Enumerate all small unit pairs and compare sum labels with complementary factor orbits."""

from collections import Counter
from fractions import Fraction
from math import gcd

if __package__:
    from .joint_sum_guess_counts import mean_rank
else:
    from joint_sum_guess_counts import mean_rank


def compare(modulus):
    units = [a for a in range(modulus) if gcd(a, modulus) == 1]
    totals = [Fraction(0) for _ in range(4)]
    for n in units:
        sums = Counter()
        orbits = Counter()
        for a in units:
            b = n * pow(a, -1, modulus) % modulus
            sums[(a + b) % modulus] += 1
            orbits[tuple(sorted((a, b)))] += 1
        for offset, labels in ((0, sums), (2, orbits)):
            _, _, best = mean_rank(Counter(labels.values()))
            totals[offset] += best
            totals[offset + 1] += Fraction(len(labels) + 1, 2)
    conditional_means = tuple(value / len(units) for value in totals)
    _, _, optimal, random = conditional_means
    kernel = sum(a * a % modulus == 1 for a in units)
    expected_saving = Fraction(len(units) - kernel, 4 * len(units))
    if random - optimal != expected_saving:
        raise AssertionError('Orbit ranks disagree with the finite-group calculation')
    return conditional_means


if __name__ == '__main__':
    for m in (25, 175):
        sum_opt, sum_random, orbit_opt, orbit_random = compare(m)
        print(f'{m=}: sum best={sum_opt} random={sum_random}; '
              f'factor orbit best={orbit_opt} random={orbit_random} saved={orbit_random-orbit_opt}')
