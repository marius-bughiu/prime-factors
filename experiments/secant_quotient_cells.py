"""Full balanced quotient sweep with a parallel strip and a lifted wheel secant."""

import argparse
import json
from math import gcd, isqrt

if __package__:
    from .quotient_search import Strip, Work, line_factors
else:
    from quotient_search import Strip, Work, line_factors


def safe_width(n, left, length, wheel, coefficient):
    """Integer width under the strict cubic condition on the span."""
    low, high = 0, length
    threshold = coefficient*(wheel*left)**3
    while low < high:
        middle = (low+high+1)//2
        if n*middle**3 < threshold:
            low = middle
        else:
            high = middle-1
    return low+1


def plan(n, wheel, max_width=False):
    """Plan the complete sweep from the product alone, without visiting a cell."""
    if n < 9 or n % 2 == 0 or wheel <= 0 or wheel % 2:
        raise ValueError("require an odd product >= 9 and a positive even wheel")
    setup_divisor = None
    while (shared := gcd(wheel, n)) > 1:
        if shared < n and setup_divisor is None:
            setup_divisor = str(shared)
        wheel //= shared
    left = max(2, isqrt((n-1)//2)+1)
    right = isqrt(n)
    # Four matches the old upper bound on area per unit of lattice index.
    # Eight uses the largest uniform width proved by the determinant bound.
    width = safe_width(n, left, right-left+1, wheel, 8 if max_width else 4)
    return left, right, width, wheel, setup_divisor


def secant_lattices(n, wheel):
    vertical = 2*wheel*wheel
    for a in range(1, wheel):
        if gcd(a, wheel) != 1:
            continue
        inverse = pow(a*(a+wheel), -1, vertical)
        slope = -(n*inverse % vertical)
        shift = n*inverse*(2*a+wheel) % vertical - vertical
        yield wheel, a, vertical, shift, slope


class ParallelStrip(Strip):
    def __init__(self, n, left, right, work, lattice):
        super().__init__(n, left, right, work, lattice)
        denominator, slope, intercept = self.upper
        # The chord error is integral, so take its exact integer upper bound.
        max_error = n*(right-left)**2//(4*left)
        self.lower = denominator, slope, intercept-max_error-1


def sweep(n, left, right, width, lattices, strip_type):
    """Sweep the specified public interval using guaranteed collinear cells."""
    work, pairs = Work(), []
    classes = 0
    for lattice in lattices:
        classes += 1
        for start in range(left, right+1, width):
            stop = min(start+width-1, right)
            box = strip_type(n, start, stop, work, lattice)
            count = box.count()
            work.blocks += 1
            work.initial_strip_points += count
            if count:
                factors = line_factors(box, count)
                if factors is None:
                    raise ArithmeticError("guaranteed collinear cell had positive rank-two determinant")
                pairs.extend((x, n//x) for x in factors)
            else:
                work.empty_strips += 1
    return dict(n=str(n), width=width, residue_classes=classes, blocks=work.blocks, bisected=work.bisected,
                floor_sums=2*work.strip_counts, euclidean_steps=work.euclidean_steps,
                moment_states=work.moment_states, initial_strip_points=work.initial_strip_points,
                quadratic_solves=work.quadratic_solves,
                pairs=[[str(x), str(y)] for x, y in sorted(pairs)])


def search(n, wheel=210, max_width=False):
    left, right, width, wheel, setup_divisor = plan(n, wheel, max_width)
    result = sweep(n, left, right, width, secant_lattices(n, wheel), ParallelStrip)
    result.update(wheel=wheel, setup_divisor=setup_divisor, max_width=max_width)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int)
    parser.add_argument("--wheel", type=int, default=210)
    parser.add_argument("--max-width", action="store_true", help="use the entire collinearity allowance")
    parser.add_argument("--plan", action="store_true", help="compute cell counts without sweeping")
    args = parser.parse_args()
    if args.plan:
        left, right, width, wheel, shared = plan(args.n, args.wheel, args.max_width)
        classes = sum(gcd(a, wheel) == 1 for a in range(1, wheel))
        result = dict(n=str(args.n), width=width, wheel=wheel, setup_divisor=shared,
                      residue_classes=classes, blocks=classes*((right-left+width)//width))
    else:
        result = search(args.n, args.wheel, args.max_width)
    print(json.dumps(result, indent=2))
