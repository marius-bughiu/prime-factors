"""Balanced weighted-sum windows from neighboring reduced fractions."""

from math import isqrt


def weighted_window(n, k, a, b):
    """Return inclusive endpoints for a primitive slope b <= a <= 2*b, b <= k.

    An empty interval has high < low. The caller supplies n > 0 and k >= 1.
    The adjacent denominator on each side is the largest up to k with the
    determinant congruence for that side.
    """
    inverse = 0 if b == 1 else pow(a, -1, b)
    gap_squares = []
    if a > b:
        neighbor = k - (k - inverse) % b
        h = b + neighbor
        gap_squares.append(b * n // (h * (h * a - 1)))
    if a < 2 * b:
        neighbor = k - (k + inverse) % b
        h = b + neighbor
        gap_squares.append(b * n // (h * (h * a + 1)))
    radicand = 4 * a * b * n
    return 1 + isqrt(radicand - 1), isqrt(radicand + max(gap_squares))
