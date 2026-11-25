"""Check a whole interval for divisors using the trace a*d+b*(N/d)."""

import argparse
import json
from math import isqrt

from experiments.universal_norm_batch import ceil_sqrt


def search(n, a, b, radius, *, max_trace_tests, modulus=None):
    """Check positive divisors in the inclusive radius around floor(sqrt(b*N/a)).

    Both weights are positive. Each parity-compatible trace consumes one test,
    including a trace rejected by the optional square-residue table. Building
    that table costs floor(modulus/2)+1 small squares when any trace is tested.
    Divisors are oriented: the value inside the interval has coefficient a.
    """
    if min(n, a, b) <= 0 or min(radius, max_trace_tests) < 0:
        raise ValueError('expected positive N and weights and nonnegative radius and trace budget')
    if modulus is not None and modulus < 2:
        raise ValueError('the square-residue modulus must be at least two')

    center = isqrt(b*n//a)
    lower = max(1, center-radius)
    upper = min(n, center+radius)
    radicand = 4*a*b*n
    first = last = None
    total = 0
    step = 2 if n % 2 else 1
    if lower <= upper:
        first = ceil_sqrt(radicand)
        first += (a+b-first) % step
        # The trace is convex on the positive real axis. Its maximum on this
        # closed interval is at an endpoint, even if the center was clipped.
        last = max(a*d+b*n//d for d in (lower, upper))
        last -= (last-first) % step
        total = max(0, (last-first)//step+1)

    tested = min(total, max_trace_tests)
    setup = 0
    square_residues = None
    if modulus is not None and tested:
        setup = modulus//2+1
        square_residues = {x*x % modulus for x in range(setup)}

    modular_tests = modular_rejections = square_tests = square_traces = 0
    hits = []
    for index in range(tested):
        trace = first+step*index
        discriminant = trace*trace-radicand
        if square_residues is not None:
            modular_tests += 1
            if discriminant % modulus not in square_residues:
                modular_rejections += 1
                continue
        square_tests += 1
        root = isqrt(discriminant)
        if root*root != discriminant:
            continue
        square_traces += 1
        numerators = (trace-root, trace+root) if root else (trace,)
        for numerator in numerators:
            divisor, remainder = divmod(numerator, 2*a)
            if not remainder and lower <= divisor <= upper and n % divisor == 0:
                hits.append(dict(trace=trace, divisor=divisor, cofactor=n//divisor))

    exhausted = tested == total
    excluded = exhausted and not hits
    status = 'partial' if not exhausted else ('excluded' if excluded else 'divisors_found')
    return dict(n=n, center=center, lower=lower, upper=upper, interval_size=max(0, upper-lower+1),
                radius=radius, a=a, b=b,
                first_trace=first, last_trace=last, trace_step=step, total_traces=total,
                max_trace_tests=max_trace_tests, tested_traces=tested, remaining_traces=total-tested,
                modulus=modulus, residue_setup_squares=setup, modular_tests=modular_tests,
                modular_rejections=modular_rejections, square_tests=square_tests, square_traces=square_traces,
                hits=hits, divisors=sorted(hit['divisor'] for hit in hits), exhausted=exhausted,
                excluded=excluded, status=status)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ('n','a','b','radius'):
        parser.add_argument(arg, type=int)
    parser.add_argument('--max-trace-tests', type=int, required=True)
    parser.add_argument('--modulus', type=int, help='test discriminants modulo this number before the square root')
    args = parser.parse_args()
    print(json.dumps(search(args.n,args.a,args.b,args.radius,max_trace_tests=args.max_trace_tests,
                            modulus=args.modulus),indent=2))
