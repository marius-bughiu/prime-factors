"""Test the upper of two predicted sums from an odd-width product residue."""

from math import isqrt


def search(n, factor_bits):
    """Assume both factors have the specified even width and n is 1 modulo 8."""
    if factor_bits < 6 or factor_bits % 2:
        raise ValueError("the factor width must be even and at least six")
    if n % 8 != 1 or not (1 << (2 * factor_bits - 2)) <= n < (1 << (2 * factor_bits)):
        raise ValueError("the product must fit the factor widths and be one modulo eight")

    precision = factor_bits + 1
    modulus = 1 << precision
    target = (n + (modulus >> 3)) % modulus
    root = 1
    for bit in range(3, precision):
        # Adding 2^(bit-1) changes bit 'bit' of an odd square and preserves lower bits.
        if ((target - root * root) >> bit) & 1:
            root += 1 << (bit - 1)

    first = (2 * root) % modulus
    predictions = sorted((first, (-first) % modulus))
    candidate = predictions[1]
    discriminant = candidate * candidate - 4 * n
    # Match the natural-number square root in ShiftedSquareSumReadout.read.
    gap = isqrt(max(discriminant, 0))
    smaller = (candidate - gap) // 2
    larger = candidate - smaller
    factor = smaller if 1 < smaller <= larger and smaller * larger == n else None
    return dict(factor=factor, factor_bits=factor_bits, precision=precision,
                root_lifts=precision - 3, sum_predictions=predictions, candidate_sum=candidate,
                discriminant=discriminant, integer_sum_checks=1)
