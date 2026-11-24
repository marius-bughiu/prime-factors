"""Compute a projected divisor coefficient from a single sparse Jacobi theta series."""

from math import isqrt


def theta_shifts(limit, residue=1):
    """Positive shifts and signs in the product for parts 0, ±residue modulo five."""
    if residue not in (1, 2):
        raise ValueError("residue must be 1 or 2")
    linear = 5 - 2 * residue
    shifts = []
    j = 1
    while True:
        small = j * (5 * j - linear) // 2
        if small > limit:
            return shifts
        sign = -1 if j % 2 else 1
        shifts.append((small, sign))
        large = small + linear * j
        if large <= limit:
            shifts.append((large, sign))
        j += 1


def logarithmic_prefix(limit, modulus, residue=1):
    """Coefficients of -xU'/U and the number of signed additions propagated."""
    if limit < 0 or modulus < 1:
        raise ValueError("limit must be nonnegative and modulus positive")
    shifts = theta_shifts(limit, residue)
    values = [0] * (limit + 1)
    for shift, sign in shifts:
        values[shift] = -shift * sign
    updates = 0
    for index in range(1, limit + 1):
        value = values[index] % modulus
        values[index] = value
        if value == 0:
            continue
        for shift, sign in shifts:
            target = index + shift
            if target > limit:
                break
            if sign < 0:
                values[target] += value
            else:
                values[target] -= value
            updates += 1
    return values, updates, sum(limit - shift for shift, _ in shifts)


def search(n, max_index):
    """For a balanced split product, unwrap its selected prime without trial division."""
    if n < 3 or n % 2 == 0 or max_index < 0:
        raise ValueError("n must be odd and at least three, and max_index nonnegative")
    modulus = 1 << (isqrt(2 * n) + 1).bit_length()
    result = dict(outcome="character", factor=None, modulus=modulus, coefficient_mod=None,
                  signed_updates=0, possible_updates=0)
    if n % 5 not in (2, 3):
        return result
    if n > max_index:
        result["outcome"] = "budget"
        return result
    prefix, updates, possible = logarithmic_prefix(n, modulus)
    value = prefix[n]
    candidate = value - 1
    result.update(outcome="residue", coefficient_mod=value,
                  signed_updates=updates, possible_updates=possible)
    if 1 < candidate < n and n % candidate == 0:
        result.update(outcome="factor", factor=candidate)
    return result
