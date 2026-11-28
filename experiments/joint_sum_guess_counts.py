"""Exact expected ranks of sum remainders for uniform local factor pairs of product one."""

from collections import Counter
from fractions import Fraction
from math import gcd, prod


def joint_histogram(primes):
    """Map multiplicity per sum to the number of sums having that multiplicity."""
    histogram = {1: 1}
    for p in primes:
        next_histogram = Counter()
        for weight, labels in histogram.items():
            next_histogram[p * weight] += 2 * labels
            next_histogram[2 * weight] += p * (p - 3) // 2 * labels
        histogram = next_histogram
    return histogram


def direct_histogram(modulus):
    """Independently enumerate each first unit and its uniquely determined partner."""
    sums = Counter(
        (a + pow(a, -1, modulus)) % modulus
        for a in range(modulus) if gcd(a, modulus) == 1
    )
    return Counter(sums.values())


def mean_rank(histogram):
    """Each label pays its inclusive stopping position in descending weight order."""
    labels = mass = rank_mass = 0
    for weight, count in sorted(histogram.items(), reverse=True):
        rank_mass += weight * count * (2 * labels + count + 1) // 2
        labels += count
        mass += weight * count
    return labels, mass, Fraction(rank_mass, mass)


def minimum_labels(histogram, coverage):
    """Take the heaviest labels first, including a partial final weight group."""
    if not 0 <= coverage <= 1:
        raise ValueError('Coverage must lie between zero and one')
    if coverage == 0:
        return 0
    pairs = sum(weight * count for weight, count in histogram.items())
    missing = (coverage.numerator * pairs + coverage.denominator - 1) // coverage.denominator
    used = 0
    for weight, count in sorted(histogram.items(), reverse=True):
        take = min(count, (missing + weight - 1) // weight)
        used += take
        missing -= take * weight
        if missing <= 0:
            return used
    raise ValueError('Coverage exceeds the available pair mass')


if __name__ == '__main__':
    for length in range(1, 6):
        primes = (5, 7, 11, 13, 17)[:length]
        modulus = prod(p**2 for p in primes)
        histogram = joint_histogram(primes)
        if length <= 3 and direct_histogram(modulus) != histogram:
            raise AssertionError('Direct sum counts differ from the product histogram')
        labels, pairs, mean = mean_rank(histogram)
        coverage = minimum_labels(histogram, Fraction(999, 1000))
        print(f'{modulus=} {labels=} {pairs=} best={mean} random={Fraction(labels+1, 2)} cover999={coverage}')
