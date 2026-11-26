"""Find a divisor using one exact binomial entry from the square-root row."""
from math import comb, gcd, isqrt


def interval(n):
    """Both prime factors are assumed distinct and of the same bit length."""
    if n < 3 or n % 2 == 0:
        raise ValueError("expected an odd number at least three")
    bits = (n.bit_length() + 1) // 2
    base = 1 << (bits - 1)
    lower = max(base, (n-1)//(2*base-1) + 1)
    return lower, isqrt(n)


def search(n, max_column):
    if max_column < 0:
        raise ValueError("expected a nonnegative column budget")
    lower, row = interval(n)
    column = max(0, row-lower+1)
    work = dict(row=str(row), lower=str(lower), column=str(column),
                max_column=max_column, coefficients_evaluated=0,
                coefficient_bits=None, residue=None)
    if column <= 0:
        return None, dict(work, outcome="empty_interval")
    if column > max_column:
        return None, dict(work, outcome="column_limit")
    coefficient = comb(row, column)
    residue = coefficient % n
    factor = gcd(residue, n)
    proper = 1 < factor < n
    return (factor if proper else None), dict(
        work, coefficients_evaluated=1, coefficient_bits=coefficient.bit_length(),
        residue=str(residue), outcome="factor" if proper else "no_split")
