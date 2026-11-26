"""Try the midpoint implied by a public cube-root estimate of the half-gap."""

from math import isqrt

from .offset_tangent_cover import cube_root


def search(n):
    if n <= 1 or n % 2 == 0:
        raise ValueError('expected an odd input greater than one')
    estimate = cube_root(4*n-1)+2
    radicand = n+estimate**2
    floor = isqrt(radicand)
    # Compare to the half integer without floating point.
    midpoint = floor + int(4*radicand > (2*floor+1)**2)
    excess = midpoint**2-n
    gap = isqrt(excess) if excess >= 0 else None
    factors = []
    if gap is not None and gap**2 == excess and 1 < midpoint-gap:
        factors = [midpoint-gap, midpoint+gap]
        if factors[0]*factors[1] != n:
            raise ArithmeticError('midpoint factors fail multiplication')
    return {'half_gap_estimate': str(estimate), 'midpoint': str(midpoint),
            'integer_cube_roots': 1, 'integer_square_roots': 1+int(gap is not None),
            'factor_candidates': 1, 'factors': list(map(str, factors)),
            'unresolved': None if factors else str(n)}
