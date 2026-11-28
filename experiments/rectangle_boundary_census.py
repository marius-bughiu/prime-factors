"""Check the fourth-root square planner and two fixed rectangles on small products."""

import json
from collections import Counter
from math import gcd, isqrt
from pathlib import Path

from experiments.circle_mark_rational_grid import nested_gcds, products
from experiments.mixed_ratio_heights import jacobi
from scripts.factor import fermat_split


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/rectangle-boundary-census.json'


def cohort(width):
    tested = 0
    midpoints = Counter()
    for n, (p, q) in products(width):
        tested += 1
        h = isqrt(isqrt(n))
        boundary = (h + 1)**2
        if p < boundary < q <= boundary + h:
            # The labels classify the product; the search receives only N and a width budget.
            divisor, steps = fermat_split(n, 1 << width)
            if divisor != p or n // divisor != q:
                raise ArithmeticError(f'Fermat found the wrong factors at {n}')
            midpoints[steps] += 1
    return dict(factor_bits=width, products=tested, mixed=sum(midpoints.values()),
                fermat_tests={str(k): v for k, v in sorted(midpoints.items())})


def shape_swap():
    n = 2491
    categories = {(True, True): 'both', (True, False): 'square_only',
                  (False, True): 'rectangle_only', (False, False): 'neither'}
    counts = dict.fromkeys(categories.values(), 0)
    examples = {}
    sparse_hits = Counter()
    for a in range(n):
        if jacobi(a, n) != -1:
            continue
        square = nested_gcds(n, a, 6, 6)[0]
        rectangle = nested_gcds(n, a, 5, 7)[0]
        if square not in (1, 47, 53) or rectangle not in (1, 47, 53):
            raise ArithmeticError(f'unexpected grid gcd at target {a}')
        counts[categories[square > 1, rectangle > 1]] += 1
        if a in (13, 29):
            examples[str(a)] = [square, rectangle]
        if square == 1:
            # For the known deficit 53 - 49 = 4, only its divisors in column 7 add hits.
            corrections = [i for i in range(1, 7) if gcd(i*i-a*7**2, n) > 1]
            if len(corrections) != 1 or corrections[0] not in (1, 2, 4):
                raise ArithmeticError(f'unexpected correction column at target {a}')
            sparse_hits[str(corrections[0])] += 1
    return dict(product=str(n), factors=['47', '53'], negative_targets=sum(counts.values()),
                hits_6_by_6=counts['both']+counts['square_only'],
                hits_5_by_7=counts['both']+counts['rectangle_only'], overlap=dict(counts),
                gcds_6_by_6_then_5_by_7=examples,
                recovered_by_numerator_in_column_7=dict(sparse_hits))


def study():
    cohorts = [cohort(width) for width in range(6, 12)]
    histogram = Counter()
    for row in cohorts:
        histogram.update(row['fermat_tests'])
    return dict(cohorts=cohorts, products=sum(r['products'] for r in cohorts),
                mixed=sum(histogram.values()), fermat_tests=dict(sorted(histogram.items())),
                shape_swap=shape_swap())


if __name__ == '__main__':
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Rectangle boundary census differs from its fixture')
    print(f"Checked {result['mixed']} mixed-boundary products among {result['products']}, "
          f"and all {result['shape_swap']['negative_targets']} negative targets at 2,491.")
