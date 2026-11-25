"""Check a short interval around a supplied center using one weighted trace.

The choice of weights uses the continued fraction of N/c², as in Hiary's
divisor-interval method (https://arxiv.org/abs/1408.2608).
"""

import argparse
import json
from math import isqrt

from experiments.continued_square import convergents


def quartile_center(n):
    """Lower quartile of the equal-bit-width smaller-factor interval."""
    if n < 1:
        raise ValueError('expected a positive input')
    bits = (n.bit_length()+1)//2
    cap = (1<<bits)-1
    lower = max(1<<(bits-1), (n+cap-1)//cap)
    upper = isqrt(n)
    if lower > upper:
        raise ValueError('equal-bit-width factor interval is empty')
    return (3*lower+upper)//4


def search(n, center, radius):
    """List every divisor in [c−W,c+W] for an odd N when the curvature bound holds.

    The supplied center satisfies c²≤N and 0<W<c. The selected denominator B
    must satisfy B*N*W²≤c²(c−W). A rejected radius produces no exclusion.
    """
    c, w = center, radius
    if n < 1 or n % 2 != 1 or not 0 < w < c or c*c > n:
        raise ValueError('expected odd N, center² ≤ N, and 0 < radius < center')
    lower, upper = c-w, c+w
    for steps, (p,q) in enumerate(convergents(n,c*c),start=1):
        if q > 2*w:
            break
        a,b = p,q
    bn = b*n
    error = a*c*c-bn
    if abs(error)*(2*w+1) > c*c:
        raise ArithmeticError('continued fraction failed the Dirichlet bound')
    if bn*w*w > c*c*lower:
        raise ValueError('radius exceeds the one-trace curvature bound for the selected weights')

    # At d=c+x, the trace minus its value at c has a linear term E*x/c²
    # and a curvature term B*N*x²/(c²*d). Thus 2*c*S is strictly between
    # 2*C−c and 2*C+3*c, where C=A*c²+B*N. There is at most one such S
    # of the prescribed parity; choose the largest one below the upper end.
    base = a*c*c+bn
    parity = a+b
    trace = parity+2*((2*base+3*c-1-2*c*parity)//(4*c))
    left = a*lower*lower+bn-trace*lower
    right = a*upper*upper+bn-trace*upper
    if a*lower*lower >= bn:
        stationary_point = 'at_or_below_lower'
        above_min = left <= 0
    elif a*upper*upper <= bn:
        stationary_point = 'at_or_above_upper'
        above_min = right <= 0
    else:
        stationary_point = 'interior'
        above_min = trace > 0 and trace*trace >= 4*a*bn
    # Convexity places the maximum at an endpoint. The preceding split uses
    # the exact continuous minimum without evaluating an irrational root.
    possible = above_min and max(left,right) >= 0
    square_tests = candidate_tests = divisor_tests = 0
    hits = []
    if possible:
        square_tests = 1
        discriminant = trace*trace-4*a*bn
        root = isqrt(discriminant)
        if root*root == discriminant:
            numerators = (trace-root, trace+root) if root else (trace,)
            for numerator in numerators:
                candidate_tests += 1
                divisor, remainder = divmod(numerator,2*a)
                if not remainder and lower <= divisor <= upper:
                    divisor_tests += 1
                    cofactor, remainder = divmod(n,divisor)
                    if not remainder:
                        hits.append(dict(trace=trace,divisor=divisor,cofactor=cofactor))
    return dict(n=n, center=c, radius=w, lower=lower, upper=upper, interval_size=2*w+1,
                a=a, b=b, signed_error=error, convergent_steps=steps,
                stationary_point=stationary_point, trace=trace, possible_traces=int(possible),
                endpoint_tests=2, square_tests=square_tests, candidate_tests=candidate_tests,
                divisor_tests=divisor_tests, hits=hits, divisors=sorted(hit['divisor'] for hit in hits),
                excluded=not hits, status='divisors_found' if hits else 'excluded')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int)
    parser.add_argument('radius',type=int)
    location = parser.add_mutually_exclusive_group(required=True)
    location.add_argument('--center',type=int)
    location.add_argument('--quartile',action='store_true',help='lower quartile under equal factor bit widths')
    args = parser.parse_args()
    center = quartile_center(args.n) if args.quartile else args.center
    print(json.dumps(search(args.n,center,args.radius),indent=2))
