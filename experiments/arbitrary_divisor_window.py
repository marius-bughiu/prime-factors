"""Check a short interval around a supplied center using one weighted trace.

The parity search approximates N/c², as in Hiary's divisor-interval method
(https://arxiv.org/abs/1408.2608). The mod-24 search approximates a shifted
ratio to enforce the congruence A + B*N = 0 modulo 12.
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


def search(n, center, radius, *, mod24=False):
    """List every divisor in [c−W,c+W] for an odd N when the curvature bound holds.

    The supplied center satisfies c²≤N and 0<W<c. The selected positive
    weights must satisfy B*N*W²≤scale*c²(c−W), with scale 1 for parity and
    12 for mod 24. The latter mode requires N coprime to six.
    """
    c, w = center, radius
    if n < 1 or n % 2 != 1 or not 0 < w < c or c*c > n:
        raise ValueError('expected odd N, center² ≤ N, and 0 < radius < center')
    if mod24 and n % 3 == 0:
        raise ValueError('mod-24 windows require N coprime to six')
    lower, upper = c-w, c+w
    scale = 12 if mod24 else 1
    shift = n % 12 if mod24 else 0
    for steps, (p,q) in enumerate(convergents(n+shift*c*c,scale*c*c),start=1):
        if q > 2*w:
            break
        a,b = scale*p-shift*q,q
    if a <= 0:
        raise ValueError('radius did not yield positive weights')
    bn = b*n
    error = a*c*c-bn
    if abs(error)*(2*w+1) > scale*c*c:
        raise ArithmeticError('continued fraction failed the Dirichlet bound')
    if bn*w*w > scale*c*c*lower:
        raise ValueError('radius exceeds the one-trace curvature bound for the selected weights')

    # At d=c+x, the trace minus its value at c has a linear term E*x/c²
    # and a curvature term B*N*x²/(c²*d). Thus 2*c*S is strictly between
    # 2*C−scale*c and 2*C+3*scale*c, where C=A*c²+B*N. In mod-24 mode
    # every divisor d satisfies d² ≡ 1 mod 24, so A*d+B*(N/d) ≡ A+B*N
    # mod 24. Choose the largest trace in the progression below its upper bound.
    base = a*c*c+bn
    residue = a+bn if mod24 else a+b
    stride = 2*scale
    trace = residue+stride*((2*base+3*scale*c-1-2*c*residue)//(2*stride*c))
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
                stationary_point=stationary_point, trace=trace, trace_stride=stride,
                possible_traces=int(possible),
                endpoint_tests=2, square_tests=square_tests, candidate_tests=candidate_tests,
                divisor_tests=divisor_tests, hits=hits, divisors=sorted(hit['divisor'] for hit in hits),
                excluded=not hits, status='divisors_found' if hits else 'excluded')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int)
    parser.add_argument('radius',type=int)
    parser.add_argument('--mod24',action='store_true',help='use the universal mod-24 trace for N coprime to six')
    location = parser.add_mutually_exclusive_group(required=True)
    location.add_argument('--center',type=int)
    location.add_argument('--quartile',action='store_true',help='lower quartile under equal factor bit widths')
    args = parser.parse_args()
    center = quartile_center(args.n) if args.quartile else args.center
    print(json.dumps(search(args.n,center,args.radius,mod24=args.mod24),indent=2))
