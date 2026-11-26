"""Group signed low carries by applying Hiary's divisor-window method to C*N.

At fixed exponent and high carry, every successful direct probe corresponds
to X*Y=C*N with X<=Y and X+Y in one known interval. The public curvature
test bounds a second weighted sum to at most two integers. Multiplying and
taking a gcd verifies each surviving candidate, including composite X,Y.
See PrimeFactors/CarryInterval.lean and https://arxiv.org/abs/1408.2608.
"""

import argparse
import json
from math import gcd, isqrt

from .continued_square import convergents
from .radix_carries import nearest


def ceil_sqrt(n):
    return 0 if n == 0 else 1 + isqrt(n - 1)


def search(n, exponent, high, low_budget):
    """Return all direct-probe successes for this carry interval when covered."""
    if n < 2 or exponent < 0 or low_budget < 0:
        raise ValueError('expected n>=2 and nonnegative exponent and low budget')
    radix = 1 << exponent
    coefficient = nearest(n, radix*radix) + high
    center_sum = coefficient*radix + nearest(n, radix)
    work = dict(geometry_sqrts=0, convergent_steps=0, trace_labels=0,
                square_tests=0, square_hits=0, root_candidates=0, divisor_tests=0, gcd_tests=0)
    result = dict(coefficient=str(coefficient), center_sum=str(center_sum),
                  low_candidates=str(2*low_budget + 1), covered=True, status='empty',
                  bounds=None, certificate=None, hits=[], work=work)
    if coefficient <= 0:
        return result

    product = coefficient*n
    first_sum = max(center_sum-low_budget, ceil_sqrt(4*product))
    last_sum = center_sum+low_budget
    work['geometry_sqrts'] = 1
    if first_sum > last_sum:
        return result
    lower = (last_sum-isqrt(last_sum**2-4*product)+1)//2
    upper = (first_sum-ceil_sqrt(first_sum**2-4*product))//2
    work['geometry_sqrts'] += 2
    result['bounds'] = dict(first_sum=str(first_sum), last_sum=str(last_sum),
                            lower=str(lower), upper=str(upper))
    if lower > upper:
        return result

    def test_divisor(x):
        if not lower <= x <= upper or x < 1:
            return
        work['divisor_tests'] += 1
        y, remainder = divmod(product, x)
        if remainder or x > y:
            return
        low = center_sum-x-y
        if abs(low) > low_budget:
            return
        work['gcd_tests'] += 1
        factor = gcd(n, y)
        if 1 < factor < n:
            result['hits'].append(dict(factor=str(factor), low=str(low),
                                       auxiliary_divisor=str(x), auxiliary_cofactor=str(y)))

    if lower == upper:
        result['status'] = 'singleton'
        test_divisor(lower)
        return result

    center = (upper+lower)//2
    radius = upper-center
    square = center*center
    a = b = 0
    for numerator, denominator in convergents(product, square):
        work['convergent_steps'] += 1
        if denominator > 2*radius:
            break
        a, b = numerator, denominator
    if min(a, b) <= 0 or abs(a*square-b*product)*(2*radius+1) > square:
        raise ArithmeticError('continued fraction failed its public approximation bound')
    result['certificate'] = dict(center=str(center), radius=str(radius), a=str(a), b=str(b))
    if radius >= center or b*product*radius*radius > square*(center-radius):
        result.update(covered=False, status='curvature_limit')
        return result

    base = a*square+b*product
    first = (2*base-center)//(2*center)+1
    last = (2*base+3*center-1)//(2*center)
    result['status'] = 'two_labels'
    candidates = set()
    for trace in range(first, last+1):
        work['trace_labels'] += 1
        delta = trace**2-4*a*b*product
        if delta < 0:
            continue
        work['square_tests'] += 1
        root = isqrt(delta)
        if root*root != delta:
            continue
        work['square_hits'] += 1
        for numerator in sorted({trace-root, trace+root}):
            work['root_candidates'] += 1
            x, remainder = divmod(numerator, 2*a)
            if not remainder:
                candidates.add(x)
    for x in sorted(candidates):
        test_divisor(x)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('exponent', type=int)
    parser.add_argument('high', type=int)
    parser.add_argument('low_budget', type=int)
    print(json.dumps(search(**vars(parser.parse_args())), indent=2))
