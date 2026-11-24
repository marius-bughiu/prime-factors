"""Recover a factor when the totient of a balanced semiprime has small squarefree part."""

from math import isqrt


def factor_from_sum(n, total):
    discriminant = total**2 - 4*n
    if discriminant < 0:
        return None
    gap = isqrt(discriminant)
    if gap**2 == discriminant and (total - gap) % 2 == 0:
        factor = (total - gap) // 2
        if 1 < factor < n and n % factor == 0:
            return factor
    return None


def search(n, max_scale):
    if n <= 1 or max_scale < 0:
        raise ValueError('the input must exceed one and the scale budget must be nonnegative')
    for scale in range(1, max_scale + 1):
        root = isqrt(n) - 1 if scale == 1 else isqrt(n // scale)
        total = n + 1 - scale * root**2
        factor = factor_from_sum(n, total)
        if factor is not None:
            return dict(factor=factor, scales_tested=scale, max_scale=max_scale)
    return dict(factor=None, scales_tested=max_scale, max_scale=max_scale)


def search_square_offset(n, max_gap):
    """Try the square corrections from the linear prime family at a fixed index-gap cap."""
    if n <= 1 or max_gap < 0:
        raise ValueError('the input must exceed one and the gap budget must be nonnegative')
    root = isqrt(n)
    residual = n - root**2
    base_sum = n + 1 - (root-1)**2
    discriminants = 0
    for gap in range(1, max_gap + 1):
        square = gap**2
        if residual % square:
            continue
        discriminants += 1
        factor = factor_from_sum(n, base_sum + square)
        if factor is not None:
            return dict(factor=factor, gaps_tested=gap, max_gap=max_gap, discriminants=discriminants)
    return dict(factor=None, gaps_tested=max_gap, max_gap=max_gap, discriminants=discriminants)
