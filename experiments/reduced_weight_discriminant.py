"""Check a stationary weighted-trace discriminant after removing its known square."""

from math import isqrt


# Test inexpensive necessary conditions first. All tables are generated from squares.
RESIDUES = tuple((m, frozenset(i*i % m for i in range(m))) for m in (64, 63, 65, 11, 17, 19))


def discriminant_root(discriminant, radix, work):
    """Return sqrt(discriminant) when integral, including zero, or None."""
    if radix <= 0:
        raise ValueError('the radix must be positive')
    reduced, remainder = divmod(discriminant, radix*radix)
    if remainder:
        raise ArithmeticError('a stationary trace discriminant must be divisible by the radix squared')
    if reduced < 0:
        return None
    full_bits = discriminant.bit_length()
    reduced_bits = reduced.bit_length()
    work['nonnegative_discriminants'] += 1
    work['full_radicand_bits'] += full_bits
    work['reduced_radicand_bits'] += reduced_bits
    work['max_full_radicand_bits'] = max(full_bits, work['max_full_radicand_bits'])
    work['max_reduced_radicand_bits'] = max(reduced_bits, work['max_reduced_radicand_bits'])
    if any(reduced % m not in squares for m, squares in RESIDUES):
        return None
    work['square_tests'] += 1
    root = isqrt(reduced)
    return radix*root if root*root == reduced else None
