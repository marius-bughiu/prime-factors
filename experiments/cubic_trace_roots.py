"""Decode cubic square traces and evaluate the two modular gcds exactly.

Run `python3 -m experiments.cubic_trace_roots` for the true and false row triples
at 989. Coefficients (a,b,c) mean X³−aX²+bX−c. Each returned rational witness
represents (v0+v1*β+v2*β²)/denominator on a supplied cubic field element β.
"""

from collections import Counter
import json
from math import gcd, isqrt

from .norm_auxiliary import integer_roots, multiply


def characteristic(d, x, y, z):
    """Characteristic coefficients of x+y*α+z*α² on α³=d."""
    return 3*x, 3*(x*x - d*y*z), x**3 + d*y**3 + d*d*z**3 - 3*d*x*y*z


def cubic(a, b, c, x):
    return ((x-a)*x+b)*x-c


def trace_roots(a, b, w, work=None):
    """All distinct integer roots of (T²−a)²−8wT−4b for a fixed signed norm w.

    The root radius R is dyadic with R²>6|a|, R³>24|w|, R⁴>3|a²−4b|.
    At |T|≥R each of the three lower terms then has magnitude <|T|⁴/3.

    A Bernstein bisection can split only when the interval interior contains a
    zero of this quartic or a nonconstant derivative. Indeed, if none vanishes,
    induction on the degree makes the derivative's Bernstein coefficients all
    weakly the same sign. The polynomial's consecutive Bernstein coefficient
    differences therefore have that sign, and its two endpoints also agree in
    weak sign. The isolator consequently keeps or discards the endpoints without
    splitting. Disjoint intervals at any depth can contain at most 4+3+2+1=10
    such zeros in total. This gives at most 1+20 ceil(log2(width)) nodes, each
    using O(1) integer operations on O(L)-bit numbers for L-bit input. Root
    isolation costs O(L³) bit operations with schoolbook multiplication.
    """
    if work is None:
        work = Counter()
    work['integer_root_nodes'] = 0
    constant = a*a - 4*b
    # Fixed cost. Surviving a small modulus is only a necessary condition.
    mask = sum(1 << t for t in range(5) if ((t*t-a)**2-8*w*t-4*b) % 5 == 0)
    work['mod5_root_mask'] = mask
    scaled = ((6*abs(a), 2), (24*abs(w), 3), (3*abs(constant), 4))
    exponent = max((v.bit_length()+degree-1)//degree for v, degree in scaled)
    radius = 1 << exponent
    width = 2*radius - 1
    work['radius'] = radius
    work['max_isolation_nodes'] = 1 + 20*(width-1).bit_length()
    if mask == 0:
        return []
    return integer_roots([constant, -8*w, -2*a, 0, 1], 1-radius, radius-1, work)


def _witness(a, b, c, u, v, w):
    """Rationalize (uβ+w)/(β+v) using the monic cubic of β."""
    common = b + a*v + v*v
    denominator = c + v*common
    if denominator == 0:
        return None
    num = [u*c + w*common, (u*v-w)*(a+v), w-u*v]
    content = gcd(abs(denominator), *num)
    signed_content = content if denominator > 0 else -content
    denominator //= signed_content
    num = [value//signed_content for value in num]
    # Check the ring identity on the supplied characteristic polynomial before
    # returning it, even when the caller supplies a reducible cubic signature.
    rem = multiply(num, num)
    rem[1] -= denominator**2
    for i in (4, 3):
        rem[i-1] += a*rem[i]
        rem[i-2] -= b*rem[i]
        rem[i-3] += c*rem[i]
    if any(rem[:3]):
        raise ArithmeticError('square witness fails reduction modulo the cubic')
    return {'numerators': num, 'denominator': denominator}


def decode(a, b, c):
    """Test a cubic field element from its characteristic coefficients alone.

    Choose the square root of nonnegative norm. Negating it gives the other
    field square root. Repeated scalar signatures need a separate test because
    a quartic root with β+v=0 need not itself be a genuine field trace.
    """
    result = {'status': 'norm_not_square', 'norm_root': None, 'roots': [], 'witnesses': [], 'work': {}}
    if c < 0 or (w := isqrt(c))**2 != c:
        return result
    result['norm_root'] = w
    work = Counter()
    roots = trace_roots(a, b, w, work)
    result.update(roots=roots, work=dict(work))
    scalar, rem = divmod(a, 3)
    if not rem and b == 3*scalar**2 and c == scalar**3:
        # A cubic field has no quadratic subfield. A rational integer which is
        # a square in it is an integer square. Only its actual trace is valid.
        root = isqrt(scalar)
        if root*root != scalar or 3*root not in roots:
            raise ArithmeticError('inconsistent scalar characteristic coefficients')
        result.update(status='scalar_square', witnesses=[{
            'trace': 3*root, 'second': 3*root*root, 'numerators': [root, 0, 0], 'denominator': 1}])
        return result
    for u in roots:
        v, odd = divmod(u*u-a, 2)
        if odd or v*v-b != 2*u*w:
            raise ArithmeticError('quartic trace violates a symmetric coefficient identity')
        witness = _witness(a, b, c, u, v, w)
        if witness is not None:
            result['witnesses'].append({'trace': u, 'second': v, **witness})
    result['status'] = 'square_witness' if result['witnesses'] else ('singular_signature' if roots else 'no_trace')
    return result


def readout(n, z, a, b, c):
    """Evaluate h(z) and h(−z) on every integral trace without modular division."""
    if n <= 1 or cubic(a, b, c, z*z % n) % n:
        raise ValueError('expected n>1 and f(z²)=0 modulo n')
    result = decode(a, b, c)
    probes = []
    divisors = set()
    for u in result['roots']:
        v = (u*u-a)//2
        values = [cubic(u, v, result['norm_root'], t) % n for t in (z % n, -z % n)]
        if values[0]*values[1] % n:
            raise ArithmeticError('modular factors fail the cubic product identity')
        gcds = [gcd(n, value) for value in values]
        divisors.update(g for g in gcds if 1 < g < n)
        probes.append({'trace': u, 'modular_values': values, 'gcds': gcds})
    return dict(result, probes=probes, proper_divisors=sorted(divisors))


if __name__ == '__main__':
    good = readout(989, 56, *characteristic(11, 49, -28, 4))
    bad = readout(989, 60, *characteristic(11, 166, -20, -23))
    print(json.dumps({'good': good, 'bad': bad}, indent=2))
