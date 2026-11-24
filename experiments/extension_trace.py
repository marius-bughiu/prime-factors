"""An exact bounded reference for the quadratic-extension trace factor formula.

For f(X)=X^3+aX+b and Jacobi(D,N)=-1, sum the Jacobi character of
Norm(f(x+y√D)) over x,y mod N. The base sum uses the same symbols as the
y=0 axis. A complete pair (A,E) permits the readout gcd(A²+E,N).
"""
from math import gcd, isqrt

from .mixed_ratio_heights import jacobi


def _setup(n, max_positions, max_selector):
    if n < 3 or n % 2 == 0 or max_positions < 0 or max_selector < 1:
        raise ValueError('expected odd N >= 3, nonnegative grid budget and positive selector limit')
    return dict(factor=None, selector=None, selector_tests=0, selector_gcds=0,
                positions=0, required_positions=str(n*n), base_symbol_evaluations=0,
                extension_symbol_evaluations=0, extension_sum=None)


def _select(n, max_selector, result):
    for d in range(2, max_selector+1):
        result['selector_tests'] += 1
        sign = jacobi(d, n)
        if sign == -1:
            result['selector'] = d
            return
        if sign == 0:
            result['selector_gcds'] += 1
            divisor = gcd(d, n)
            if 1 < divisor < n:
                result.update(factor=divisor, outcome='selector_divisor')
                return
    result['outcome'] = 'selector_limit'


def _complete_sums(n, a, b, max_positions, result, *, punctured):
    d = result['selector']
    positions = min(n*n, max_positions)
    a, b = a % n, b % n
    base = marked = extension = 0
    rows = (positions+n-1)//n
    for x in range(rows):
        xx = x*x % n
        value = x*(xx+a)+b
        symbol = jacobi(value, n)
        base += symbol
        if punctured:
            symbol = jacobi((x-2)**2 * value, n)
            marked += symbol
        extension += symbol*symbol
        for y in range(1, min(n, positions-x*n)):
            dyy = d*y*y % n
            real = (x*(xx+3*dyy+a)+b) % n
            imag = y*(3*xx+dyy+a) % n
            norm = real*real - d*imag*imag
            if punctured:
                norm *= pow((x-2)**2 - dyy, 2, n)
            extension += jacobi(norm, n)
    result.update(positions=positions, base_symbol_evaluations=2*rows if punctured else rows,
                  extension_symbol_evaluations=positions-rows)
    if positions < n*n:
        result['outcome'] = 'position_limit'
        return None
    return base, marked, extension


def search(n, max_positions, max_selector, a=1, b=1):
    """Count one grid position per symbol, separately from selector symbols."""
    result = _setup(n, max_positions, max_selector)
    # The remaining discriminant factor -16 is a unit modulo this odd N.
    disc_gcd = gcd(4*pow(a, 3, n) + 27*pow(b, 2, n), n)
    result.update(discriminant_gcd=str(disc_gcd), base_sum=None, trace_gcd=None)
    if disc_gcd == n:
        return dict(result, outcome='singular_curve')
    if disc_gcd > 1:
        return dict(result, factor=disc_gcd, outcome='discriminant_divisor')
    _select(n, max_selector, result)
    if result['selector'] is None:
        return result
    sums = _complete_sums(n, a, b, max_positions, result, punctured=False)
    if sums is None:
        return result

    base, _, extension = sums
    divisor = gcd(base*base+extension, n)
    factor = divisor if 1 < divisor < n else None
    return dict(result, factor=factor, base_sum=str(base), extension_sum=str(extension),
                trace_gcd=str(divisor), outcome='trace_divisor' if factor else 'no_split')


def punctured_search(n, max_positions, max_selector):
    """Recover a verified divisor from (x−2)²(x³−x) and x³−x."""
    result = _setup(n, max_positions, max_selector)
    result.update(normalizing_sign=jacobi(6, n), normalized_base_sum=None,
                  normalized_marked_sum=None, local_traces=None, assignments_tested=0)
    if result['normalizing_sign'] == 0:
        divisor = gcd(6, n)
        if divisor < n:
            return dict(result, factor=divisor, outcome='mark_divisor')
        return dict(result, outcome='invalid_mark')
    _select(n, max_selector, result)
    if result['selector'] is None:
        return result
    sums = _complete_sums(n, -1, 0, max_positions, result, punctured=True)
    if sums is None:
        return result

    base, marked, extension = sums
    base *= result['normalizing_sign']
    marked *= result['normalizing_sign']
    result.update(normalized_base_sum=str(base), normalized_marked_sum=str(marked),
                  extension_sum=str(extension))
    total = base + 1 - marked
    discriminant = total*total - 4*base
    if discriminant < 0:
        return dict(result, outcome='no_split')
    difference = isqrt(discriminant)
    if difference*difference != discriminant or (total-difference) % 2:
        return dict(result, outcome='no_split')
    roots = [(total-difference)//2, (total+difference)//2]
    result['local_traces'] = [str(t) for t in roots]
    for split in dict.fromkeys(roots):
        result['assignments_tested'] += 1
        inert = total-split
        denominator = (split-1)**2
        if denominator == 0 or extension % denominator:
            continue
        twice_prime = extension//denominator + inert*inert + 1
        if twice_prime % 2:
            continue
        candidate = twice_prime//2
        if 1 < candidate < n and n % candidate == 0:
            return dict(result, factor=candidate, outcome='punctured_divisor')
    return dict(result, outcome='no_split')
