"""Read a decoded square in the original cubic power basis.

The search supplies a cubic f, a root m modulo n, an integer z, and a field
element beta specializing to z². A square witness from the trace decoder is
expressed on 1, beta, beta². Changing back to 1, alpha, alpha² can cancel a
denominator that is a multiple of both hidden primes.
"""

from math import gcd, isqrt

from .cubic_trace_roots import trace_roots
from .cubic_trace_search import characteristic, evaluate, multiply_by_alpha


def product(f, left, right):
    """Multiply two elements modulo the supplied monic cubic."""
    middle = multiply_by_alpha(f, right)
    high = multiply_by_alpha(f, middle)
    return tuple(left[0]*u + left[1]*v + left[2]*w for u, v, w in zip(right, middle, high))


def direct_readout(n, m, f, beta, z, witness):
    """Return a primitive field square root and both specialization gcds."""
    if n <= 1 or evaluate(f, m) % n:
        raise ValueError('the public base must be a root of f modulo n')
    if (beta[0]+m*(beta[1]+m*beta[2])-z*z) % n:
        raise ValueError('the element must specialize to the supplied square')
    t0, t1, t2 = witness['numerators']
    denom = witness['denominator']
    if denom <= 0:
        raise ValueError('the witness denominator must be positive')
    square = product(f, beta, beta)
    num = [t1*x+t2*y for x, y in zip(beta, square)]
    num[0] += t0
    common = gcd(denom, *num)
    coeffs = tuple(x//common for x in num)
    denom //= common
    if product(f, coeffs, coeffs) != tuple(denom*denom*x for x in beta):
        raise ValueError('the proposed root fails its square identity in the original basis')
    value = (coeffs[0]+m*(coeffs[1]+m*coeffs[2])) % n
    divisors = [gcd(n, value-s*denom*z) for s in (1, -1)]
    return {'coefficients': list(coeffs), 'denominator': denom, 'cancelled_content': common,
            'specialized_numerator': value, 'denominator_gcd': gcd(n, denom), 'gcds': divisors}


def projected_readout(n, m, f, beta, z):
    """Use one trace quartic on G_m(alpha)^2 beta without reconstructing a field root."""
    value_f = evaluate(f, m)
    if n <= 1 or value_f == 0 or value_f % n:
        raise ValueError('f(m) must be a nonzero multiple of n')
    if (beta[0]+m*(beta[1]+m*beta[2])-z*z) % n:
        raise ValueError('the element must specialize to the supplied square')
    _, linear, quadratic = f
    derivative = 3*m*m+2*quadratic*m+linear
    projector = (m*m+quadratic*m+linear, m+quadratic, 1)
    masked = product(f, product(f, projector, projector), beta)
    a, b, c = characteristic(f, masked)
    _, _, original_norm = characteristic(f, beta)
    if c != value_f**4*original_norm or (a-(derivative*z)**2) % n or b % n:
        raise ArithmeticError('projected characteristic coefficients fail the rank-one identity')
    work, traces, gcds = {}, [], []
    if c >= 0 and (w := isqrt(c))**2 == c:
        traces = trace_roots(a, b, w, work)
        if masked[1:] == (0, 0):
            # In a cubic field a scalar square of square norm is an integer square.
            traces = [u for u in traces if u == 3*isqrt(masked[0])]
        for u in traces:
            if (u*u-(derivative*z)**2) % n:
                raise ArithmeticError('projected trace fails the square congruence')
            gcds.append([gcd(n, u-s*derivative*z) for s in (1, -1)])
    return {'derivative': derivative, 'derivative_gcd': gcd(n, derivative),
            'masked_element': list(masked), 'signed_traces': traces, 'gcds': gcds, 'work': work}
