"""Exact bounded checks for CircularCoefficientFilter. Uses only Python's standard library."""

from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import isqrt


@lru_cache(maxsize=None)
def retained(cutoff, n):
    """Sum both members of each divisor pair above the cutoff, counting a square once."""
    total = 0
    for divisor in range(cutoff + 1, isqrt(n) + 1):
        cofactor, remainder = divmod(n, divisor)
        if remainder == 0:
            total += divisor
            if cofactor != divisor:
                total += cofactor
    return total


def multiply(left, right):
    """Multiply complex numbers given by an exact real and imaginary part."""
    a, b = left
    c, d = right
    return a*c - b*d, a*d + b*c


def check_four_samples(target, cutoff, degree):
    coefficients = [retained(cutoff, n) for n in range(degree + 1)]
    roots = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    real_sum = imag_sum = 0
    for step, (x, y) in enumerate(roots):
        point = Fraction(x, 2), Fraction(y, 2)
        real = imag = 0
        for coefficient in reversed(coefficients):
            real, imag = multiply((real, imag), point)
            real += coefficient
        real, imag = multiply((real, imag), roots[(-step*target) % 4])
        real_sum += real
        imag_sum += imag

    normalized = real_sum * Fraction(2**target, 4)
    residue_sum = sum(Fraction(coefficients[n] * 2**target, 2**n)
                      for n in range(target % 4, degree + 1, 4))
    assert imag_sum == 0 and normalized == residue_sum
    return normalized


def check_neighbours():
    """Compare the explicit nearby witnesses with direct divisor enumeration."""
    primes = [p for p in range(3, 128, 2)
              if all(p % d for d in range(2, isqrt(p) + 1))]
    cases = 0
    for p, q in combinations(primes, 2):
        n = p*q
        for samples in range(1, 9):
            for cutoff in range(1, min(p, 9)):
                if (cutoff + samples)**2 >= n:
                    continue
                quotient = (cutoff + samples - 1) // samples
                divisor = 1 + quotient*samples
                residue = (n*quotient) % divisor
                steps_down = divisor - residue
                steps_up = residue or divisor
                earlier = n - steps_down*samples
                later = n + steps_up*samples
                assert earlier % divisor == later % divisor == 0
                assert retained(cutoff, n) == p + q
                assert retained(cutoff, earlier) >= earlier // divisor > cutoff
                assert retained(cutoff, later) >= later // divisor > cutoff
                cases += 1
    return cases


if __name__ == "__main__":
    estimate = check_four_samples(target=77, cutoff=2, degree=140)
    contribution = retained(2, 65) * 2**(77 - 65)
    cases = check_neighbours()
    assert (retained(2, 77), contribution, cases) == (18, 73_728, 24_920)
    print(f"Four-sample projection through degree 140 = {estimate}")
    print(f"Coefficient at 77 = 18. Contribution from 65 alone = {contribution:,}.")
    print(f"Nearby coefficients checked on {cases:,} product, cutoff and grid choices.")
