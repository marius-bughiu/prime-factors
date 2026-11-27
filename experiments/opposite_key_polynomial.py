"""Detect opposite nonzero residues using the even and odd halves of a split polynomial."""
from math import gcd

from experiments.wide_modulus import product_tree


def trim(coefficients):
    while coefficients and coefficients[-1] == 0:
        coefficients.pop()
    return coefficients


def opposite_factor(values, n, work):
    """Requires a mixed semiprime and regular original labels, as in the directed product."""
    points = [(2*u-1) % n for u in values]
    f = product_tree(points, n)[-1][0]
    mid = gcd(f[0], n)
    work['euclid_gcds'] += 1
    if 1 < mid < n:
        work['source'] = 'constant term'
        return mid
    if mid == n:
        raise ArithmeticError('a regular middle label cannot occur at the nonsquare-three prime')

    a, b = trim(f[0::2]), trim(f[1::2])
    if len(a) < len(b):
        a, b = b, a
    while b:
        if len(b) == 1:
            divisor = gcd(b[0], n)
            work['euclid_gcds'] += 1
            if divisor > 1:
                work['source'] = 'constant remainder'
                return divisor
            return None
        try:
            inverse = pow(b[-1], -1, n)
        except ValueError:
            work['euclid_gcds'] += 1
            work['source'] = 'noninvertible leading coefficient'
            return gcd(b[-1], n)
        work['euclid_inversions'] += 1
        while len(a) >= len(b):
            shift = len(a)-len(b)
            scale = a[-1]*inverse % n
            for i in range(len(b)-1):
                a[shift+i] = (a[shift+i]-scale*b[i]) % n
            work['coefficient_updates'] += len(b)-1
            a.pop()
            trim(a)
        a, b = b, a
    if len(a) > 1:
        raise ArithmeticError('a common nonconstant divisor cannot survive the nonsquare-three reduction')
    return None
