"""Bounded Fermat search by lifting square roots modulo successive even powers of five."""

from math import isqrt


def search(n, max_exponent, per_root):
    """At level v test per_root midpoints per solution of h² = n (mod 5**(2*v))."""
    if n < 3 or n % 2 == 0 or max_exponent < 0 or per_root < 0:
        raise ValueError('expected an odd input above one and nonnegative search budgets')
    if n % 5 == 0 or per_root == 0:
        factor = 5 if n > 5 and n % 5 == 0 else None
        return dict(factor=factor, exponent=0, square_tests=0, lift_tests=0,
                    max_exponent=max_exponent, per_root=per_root)
    start = isqrt(n - 1) + 1
    roots = [0]
    modulus = 1
    tests = lifts = 0
    for v in range(max_exponent + 1):
        if v:
            for _ in range(2):
                next_modulus = 5 * modulus
                candidates = [u + j * modulus for u in roots for j in range(5)]
                lifts += len(candidates)
                roots = [u for u in candidates if (start + u)**2 % next_modulus == n % next_modulus]
                modulus = next_modulus
            if not roots:
                break
        for offset in roots:
            for j in range(per_root):
                midpoint = start + offset + j * modulus
                # At and beyond (n+1)/2 only the trivial odd pair or no pair can occur.
                if 2 * midpoint >= n + 1:
                    break
                tests += 1
                delta = midpoint**2 - n
                half_gap = isqrt(delta)
                if half_gap**2 == delta:
                    return dict(factor=midpoint-half_gap, exponent=v, square_tests=tests,
                                lift_tests=lifts, max_exponent=max_exponent, per_root=per_root)
    return dict(factor=None, exponent=v, square_tests=tests, lift_tests=lifts,
                max_exponent=max_exponent, per_root=per_root)
