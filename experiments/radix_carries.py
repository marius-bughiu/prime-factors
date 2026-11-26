"""Test the two rounded product digits in PrimeFactors.PredictedTraceCarries."""

from math import gcd, isqrt


def nearest(n, d):
    """Return the nearest quotient for positive d, rounding half ties upward."""
    return (2 * n + d) // (2 * d)


def search(n, high_budget, low_budget):
    """Try increasing dyadic radices, using only n and the two carry limits."""
    if n < 2 or min(high_budget, low_budget) < 0:
        raise ValueError("expected n >= 2 and nonnegative carry limits")
    bits = n.bit_length()
    work = dict(radices=0, candidates=0, square_tests=0, square_hits=0, hit=None)
    for exponent in range(bits // 4 + 1, (bits + 1) // 2 + 1):
        radix = 1 << exponent
        leading = nearest(n, radix * radix)
        middle = nearest(n, radix)
        work["radices"] += 1
        for high in range(-high_budget, high_budget + 1):
            coefficient = leading + high
            for low in range(-low_budget, low_budget + 1):
                work["candidates"] += 1
                trace = coefficient * radix + middle - low
                if coefficient <= 0 or trace <= 0:
                    continue
                # The discriminant is unchanged when the variable is shifted
                # by the radix. These smaller coefficients save large products.
                linear = middle - low - coefficient * radix
                constant = n - radix * (middle - low)
                delta = linear * linear - 4 * coefficient * constant
                if delta < 0:
                    continue
                work["square_tests"] += 1
                root = isqrt(delta)
                if root * root != delta:
                    continue
                work["square_hits"] += 1
                if (trace + root) % 2:
                    continue
                divisor = gcd(n, (trace + root) // 2)
                if 1 < divisor < n:
                    work["hit"] = dict(exponent=exponent, high=high, low=low)
                    return divisor, work
    return None, work
