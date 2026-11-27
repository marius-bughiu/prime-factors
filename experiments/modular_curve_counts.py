"""Count projective cosets from small levels. Run python3 -m experiments.modular_curve_counts."""

import argparse
import json
from math import gcd
from pathlib import Path

from experiments.predecessor_square import factor_from_sum

FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/modular-curve-counts.json'


def coset_counts(level):
    """Enumerate the primitive projective columns modulo level using the generators S and T."""
    if level < 2:
        raise ValueError('the level must be at least two')
    odd_part = level // (level & -level)
    work = dict(normalizations=0, unit_gcd_tests=0, modular_inverses=0,
                max_gcd_tests_per_normalization=0)
    first_factor = None

    def normalize(x, y):
        nonlocal first_factor
        work['normalizations'] += 1
        # Primitive columns admit a unit x+t*y by CRT. Multiplying the column by a
        # unit preserves the first admissible t, so this gives a unique representative.
        for t in range(level):
            value = (x + t*y) % level
            common = gcd(value, level)
            work['unit_gcd_tests'] += 1
            if common == 1:
                inverse = pow(value, -1, level)
                work['modular_inverses'] += 1
                work['max_gcd_tests_per_normalization'] = max(
                    work['max_gcd_tests_per_normalization'], t + 1)
                return x*inverse % level, y*inverse % level
            if first_factor is None:
                divisor = common // (common & -common)
                if 1 < divisor < odd_part:
                    first_factor = dict(divisor=divisor, normalization=work['normalizations'],
                                        unit_gcd_test=work['unit_gcd_tests'])
        raise ArithmeticError('generator produced a nonprimitive column')

    points = [(1, 0)]
    indices = {points[0]: 0}
    s, t = [], []
    # New points extend this breadth-first traversal. The start is the line at infinity.
    for x, y in points:
        for permutation, image in ((s, (-y, x)), (t, (x+y, y))):
            target = normalize(*image)
            if target not in indices:
                indices[target] = len(points)
                points.append(target)
            permutation.append(indices[target])

    index = len(points)
    e2 = sum(i == s[i] for i in range(index))
    e3 = sum(i == s[t[i]] for i in range(index))
    seen = bytearray(index)
    widths = []
    for start in range(index):
        if seen[start]:
            continue
        j, width = start, 0
        while not seen[j]:
            seen[j] = 1
            width += 1
            j = t[j]
        if j != start:
            raise ArithmeticError('translation failed to permute the projective line')
        widths.append(width)
    numerator = 12 + index - 3*e2 - 4*e3 - 6*len(widths)
    genus, remainder = divmod(numerator, 12)
    if remainder or genus < 0:
        raise ArithmeticError('inconsistent coset counts in the genus formula')
    return dict(level=level, index=index, order_two_points=e2, order_three_points=e3,
                cusps=len(widths), cusp_widths=sorted(widths), genus=genus,
                work=work, first_normalization_factor=first_factor)


def factors_from_divisor_sum(n, divisor_sum):
    """Decode under the distinct-prime promise and verify that the returned pair divides n."""
    p = factor_from_sum(n, divisor_sum - n - 1)
    return None if p is None else [p, n//p]


def level_four(n):
    counts = coset_counts(4*n)
    divisor_sum = 2*counts['genus'] + 10
    return dict(n=n, counts=counts, divisor_sum=divisor_sum, factor_sum=divisor_sum-n-1,
                factors=factors_from_divisor_sum(n, divisor_sum))


def rounded_divisor_sum(observation, a):
    """Round (g+8A−1)/A² to a multiple of four; ties resolve upwards."""
    if a < 1 or a & (a-1):
        raise ValueError('A must be a positive power of two')
    spacing = 4*a*a
    return 4*((observation + 8*a - 1 + spacing//2)//spacing)


def dyadic_example(n, a):
    if a < 1 or a & (a-1):
        raise ValueError('A must be a positive power of two')
    counts = coset_counts(8*a*a*n)
    genus = counts['genus']
    radius = 2*a*a
    divisor_sum = rounded_divisor_sum(genus, a)
    if genus != a*a*divisor_sum - 8*a + 1:
        raise ArithmeticError('genus is outside the promised dyadic progression')
    # These are deliberately perturbed observations of an already enumerated genus.
    offsets = (-radius-1, -radius, -radius+1, 0, radius-1, radius, radius+1)
    rounding = [dict(error=e, divisor_sum=rounded_divisor_sum(genus+e, a)) for e in offsets]
    return dict(n=n, a=a, counts=counts, divisor_sum=divisor_sum,
                factors=factors_from_divisor_sum(n, divisor_sum), rounding=rounding)


def report():
    return dict(odd_level=coset_counts(527), four_times_product=level_four(527),
                dyadic_levels=[dyadic_example(15, a) for a in (1, 2, 4)])


def check_fixture(measured, cases):
    """Check the completed discoveries against the independent benchmark."""
    runs = [measured['four_times_product'], *measured['dyadic_levels']]
    rows = []
    for run in runs:
        n, counts, pair = run['n'], run['counts'], run['factors']
        if pair is None or len(pair) != 2 or min(pair) <= 1 or pair[0]*pair[1] != n:
            raise ArithmeticError(f'incomplete factorization of {n} at level {counts["level"]}')
        rows.append(dict(n=str(n), level=counts['level'], factors=[str(p) for p in pair],
                         genus=counts['genus'], work=counts['work'],
                         first_normalization_factor=counts['first_normalization_factor']))
    if rows != cases:
        raise ValueError('modular-curve counts differ from the benchmark fixture')


def certify_report(measured):
    """Replay each distinct discovered factorization with the project's Lean checker."""
    from tempfile import TemporaryDirectory
    from scripts.factor import render_certificate, verify_file

    runs = [measured['four_times_product'], *measured['dyadic_levels']]
    pairs = {(run['n'], tuple(run['factors'])) for run in runs}
    with TemporaryDirectory() as directory:
        for n, pair in sorted(pairs):
            path = Path(directory) / f'Factor{n}.lean'
            path.write_text(render_certificate(n, list(pair)))
            verify_file(path)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='check the bounded benchmark fixture')
    parser.add_argument('--verify', action='store_true', help='check the fixture and Lean-certify its discoveries')
    args = parser.parse_args()
    measured = report()
    if args.check or args.verify:
        check_fixture(measured, json.loads(FIXTURE.read_text()))
    if args.verify:
        certify_report(measured)
    print(json.dumps(measured, indent=2))
