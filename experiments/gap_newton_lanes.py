"""Compare ordinary, gap-power and Dickson coordinates for signed Newton factor lanes."""

import argparse
import json
from math import comb, isqrt, prod
from pathlib import Path
from statistics import median
from tempfile import TemporaryDirectory
from time import perf_counter

from .midpoint_weights import smooth_radix
from .newton_lanes import coprime_factorials, minimum_radix
from .norm_auxiliary import reduced_basis
from .quartic_factor_lanes import certified_eliminant, lane_basis, run_lanes, search as ordinary_search
from scripts.factor import render_certificate, verify_file


def gap_monomials(n, power):
    """Rows for 1, D, x, D², xD, ... in y^power,...,1,...,x^power, with D=x−y."""
    constant = [0]*(2*power+1)
    constant[power] = 1
    rows = [constant]
    for j in range(1, power+1):
        for x_power in (0, 1):
            degree = j-x_power
            row = [0]*len(constant)
            for b in range(degree+1):
                a = j-b
                row[power+a-b] += (-1)**b*comb(degree, b)*n**min(a, b)
            rows.append(row)
    return rows


def gap_coordinates(original, transform):
    """Recover integral coefficients using the two outer monomials at each degree."""
    power = len(original)//2
    remainder = list(original)
    coordinates = [0]*len(original)
    for j in range(power, 0, -1):
        a = (-1)**j*remainder[power-j]
        b = remainder[power+j]-a
        coordinates[2*j-1:2*j+1] = a, b
        left, right = transform[2*j-1:2*j+1]
        for k in range(power-j, power+j+1):
            remainder[k] -= a*left[k]+b*right[k]
    coordinates[0] = remainder[power]
    return coordinates


def gap_scales(n, power):
    x, gap = isqrt(2*n), isqrt(n//2)
    return [1]+[s for j in range(1, power+1) for s in (gap**j, x*gap**(j-1))]


def dickson_basis(n, power):
    """Replace D^j by P_j(D), monic of degree j with sup norm 2*s^j on [-2s,2s]."""
    s = max(1, isqrt(n//8))  # D is even, so |D| <= 2*floor(sqrt(n/8)).
    plain = gap_monomials(n, power)
    gap_powers = [plain[0], *plain[1::2]]
    x_gap_powers = plain[2::2]
    transform, scales = [plain[0]], [1]
    previous, current = [2], [0, 1]
    for j in range(1, power+1):
        # The companion at degree one is x, whereas the recurrence starts at P_0=2.
        for rows, poly in ((gap_powers, current), (x_gap_powers, [1] if j == 1 else previous)):
            columns = zip(*rows[:len(poly)])
            transform.append([sum(c*entry for c,entry in zip(poly,col)) for col in columns])
        scales.extend((2*s**j, isqrt(2*n)*(1 if j == 1 else 2*s**(j-1))))
        following = [0, *current]
        for k,c in enumerate(previous):
            following[k] -= s*s*c
        previous, current = current, following
    return transform, scales


def equation(n, u, radix, power, factorials, transform, scales, work):
    """Reduce in gap coordinates, then verify the eliminant on the full Newton grid."""
    monomials = lane_basis(n, u, radix, power, factorials)
    coordinates = [gap_coordinates(row, transform) for row in monomials]
    weighted = [[c*s for c,s in zip(row, scales)] for row in coordinates]
    # Track the original Laurent coefficients through the same integer row operations.
    vectors, originals = reduced_basis(weighted, work, initial_coefficients=monomials)
    best = min(range(len(vectors)), key=lambda i: sum(map(abs, vectors[i])))
    selected = originals[best]
    scaled = [c*s for c,s in zip(gap_coordinates(selected, transform), scales)]
    degree = 2*power
    modulus = radix**degree*factorials[-1]
    if scaled != vectors[best] or not any(selected) or sum(map(abs, scaled)) >= modulus:
        raise ArithmeticError('failed to certify the absolute gap trace bound')
    return certified_eliminant(n, u, radix, power, selected, modulus, check_values=True)


def search(n, max_orbits=None, *, power=2, basis='gap'):
    if n < 3 or n % 2 == 0 or power < 1 or (max_orbits is not None and max_orbits < 0):
        raise ValueError('expected odd n >= 3, positive power and nonnegative optional budget')
    factorials = coprime_factorials(n, 2*power)
    if basis == 'gap':
        transform, scales = gap_monomials(n, power), gap_scales(n, power)
    elif basis == 'dickson':
        transform, scales = dickson_basis(n, power)
    else:
        raise ValueError('expected gap or dickson coordinates')
    target = minimum_radix(prod(scales), factorials)
    radix = smooth_radix(n, target)
    upper = isqrt(2*n)

    def build_equation(u, work):
        return equation(n, u, radix, power, factorials, transform, scales, work)

    result = run_lanes(n, max_orbits, power, upper, radix, True, build_equation)
    result.update(basis=f'{basis}-newton', gap_bound=isqrt(n//2), minimum_radix=target)
    return result


def compare(n, cap, repetitions, rotation, methods=('ordinary', 'gap')):
    times = {name: [] for name in methods}
    runs = {}
    for i in range(repetitions):
        lead = (i+rotation) % len(methods)
        order = methods[lead:]+methods[:lead]
        for method in order:
            start = perf_counter()
            result = (ordinary_search(n, cap, signed=True, basis='newton') if method == 'ordinary'
                      else search(n, cap, basis=method))
            times[method].append(perf_counter()-start)
            if method in runs and runs[method] != result:
                raise ArithmeticError('nondeterministic search output')
            runs[method] = result
    for method,result in runs.items():
        result['median_seconds'] = median(times[method])
    return runs


def panel(methods=('ordinary', 'gap')):
    directory = Path(__file__).resolve().parents[1]/'research'
    inputs = json.loads((directory/'quartic-lane-holdout.json').read_text())['rows']
    rows = []
    with TemporaryDirectory() as temp:
        source = Path(temp)/'Factorization.lean'
        for i,case in enumerate(inputs):
            n = int(case['n'])
            runs = compare(n, None, 3, i, methods)
            if any(r['pairs'] != [case['expected_factors']] or r['remaining_orbits'] or
                   r['ordinary_total_orbits'] != r['ordinary_covered_orbits'] for r in runs.values()):
                raise ArithmeticError('incomplete coverage or incorrect pair on the holdout')
            factors = runs['gap']['pairs'][0]
            source.write_text(render_certificate(n, list(map(int, factors))))
            verify_file(source)
            rows.append(dict(sample=case['sample'], n=case['n'], certified_factors=factors, methods=runs))
    n = int(json.loads((directory/'certified-control.json').read_text())['product'])
    partial = compare(n, 2, 1, 0, methods)
    if any(r['visited_orbits'] != 2 or r['remaining_orbits'] <= 0 or r['pairs'] for r in partial.values()):
        raise ArithmeticError('the two-group outcome changed on the certified control')
    return dict(power=2, signed=True, repetitions=3, rows=rows, control_commit='4699aab',
                capped_2048=dict(n=str(n), remaining_cofactor=str(n), max_orbits=2,
                                 repetitions=1, methods=partial))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', nargs='?', type=int, help='omit to replay the fixed comparison')
    parser.add_argument('--power', type=int, default=2)
    parser.add_argument('--max-orbits', type=int)
    parser.add_argument('--dickson', action='store_true', help='use the centered Dickson gap basis')
    args = parser.parse_args()
    if args.n is None:
        result = panel(('ordinary', 'gap', 'dickson') if args.dickson else ('ordinary', 'gap'))
    else:
        result = search(args.n, args.max_orbits, power=args.power, basis='dickson' if args.dickson else 'gap')
    print(json.dumps(result, indent=2))
