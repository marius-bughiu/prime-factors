"""Evaluate Dickson traces at public labels by a binary Lucas ladder."""

from math import gcd


def trace_power(x, d, n):
    """Compute D_d(x) modulo n, starting at the pair (D_1, D_2)."""
    if d < 0 or n < 2:
        raise ValueError("nonnegative degree and modulus at least two required")
    if d == 0:
        return 2 % n
    x %= n
    a, b = x, (x * x - 2) % n
    for bit in bin(d)[3:]:
        adjacent = (a * b - x) % n
        if bit == "0":
            a, b = (a * a - 2) % n, adjacent
        else:
            a, b = adjacent, (b * b - 2) % n
    return a


def search(n, exponent, start, max_seeds):
    """Try public labels in increasing order and return the first proper gcd."""
    if n < 3 or start < 0 or max_seeds < 0:
        raise ValueError("invalid product, first label or label budget")
    degrees = {"square-1": n * n - 1, "minus": n - 1, "plus": n + 1,
               "monomial-square-1": n * n - 1}
    degree = degrees[exponent]
    work = {"labels": 0, "gcds": 0, "ladder_steps": 0, "modular_powers": 0}
    seed = None
    for seed in range(start, start + max_seeds):
        work["labels"] += 1
        if exponent == "monomial-square-1":
            value = pow(seed, degree, n) - 1
            work["modular_powers"] += 1
        else:
            value = trace_power(seed, degree, n) - 2
            work["ladder_steps"] += degree.bit_length() - 1
        divisor = gcd(value, n)
        work["gcds"] += 1
        if 1 < divisor < n:
            return {"outcome": "factor", "factor": min(divisor, n // divisor),
                    "work": work, "seed": seed}
    return {"outcome": "budget", "factor": None, "work": work, "seed": seed}
