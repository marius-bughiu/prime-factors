"""Recover a factor when the totient of a balanced semiprime has small squarefree part."""

from math import isqrt


def search(n, max_scale):
    if n <= 1 or max_scale < 0:
        raise ValueError('the input must exceed one and the scale budget must be nonnegative')
    for scale in range(1, max_scale + 1):
        root = isqrt(n) - 1 if scale == 1 else isqrt(n // scale)
        total = n + 1 - scale * root**2
        discriminant = total**2 - 4*n
        if discriminant < 0:
            continue
        gap = isqrt(discriminant)
        if gap**2 == discriminant and (total - gap) % 2 == 0:
            factor = (total - gap) // 2
            if 1 < factor < n and n % factor == 0:
                return dict(factor=factor, scales_tested=scale, max_scale=max_scale)
    return dict(factor=None, scales_tested=max_scale, max_scale=max_scale)
