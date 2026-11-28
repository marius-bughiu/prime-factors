"""Exact target frequencies and product-only searches on bounded prime-product cohorts.

Each input N uses h = floor(N^(1/4)). The product alone selects the first
negative-Jacobi target and determines the grid and Fermat searches. Prime
labels independently classify the input and give exact CRT target counts.
"""

import json
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import isqrt
from pathlib import Path

from experiments.circle_mark_prefix_skip import choose_target
from experiments.circle_mark_rational_grid import nested_gcds, products
from experiments.mixed_ratio_heights import jacobi
from scripts.factor import fermat_split


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/public-grid-targets.json'


@lru_cache(maxsize=None)
def local_square_count(r, h):
    numerators = [i*i % r for i in range(1, h+1)]
    inverse_squares = [pow(j*j, -1, r) for j in range(1, h+1)]
    return len({u*v % r for u in numerators for v in inverse_squares})


@dataclass(frozen=True)
class Observation:
    n: int
    p: int
    q: int
    h: int
    target: int
    divisor: int
    gcd_tests: int
    fermat_steps: int
    hits_at_p: int
    hits_at_q: int
    negative_targets: int

    @property
    def rate(self):
        return Fraction(self.hits_at_p + self.hits_at_q, self.negative_targets)

    @property
    def region(self):
        boundary = (self.h+1)**2
        if self.q < boundary:
            return 'below_boundary'
        if self.q <= boundary + self.h:
            return 'small_deficit'
        return 'beyond_band'


def observe(n, p, q):
    h = isqrt(isqrt(n))
    a, selector_factor = choose_target(n)
    if selector_factor is not None:
        raise ArithmeticError(f'Target selection found a factor first at {n}')
    divisor, gcd_tests, _ = nested_gcds(n, a, h, h)
    smaller, steps = fermat_split(n, 1 << ((n.bit_length()+1)//2))
    if divisor not in (1, p, q) or smaller != p or n // smaller != q:
        raise ArithmeticError(f'Product-only search disagrees with prime labels at {n}')

    # The other prime must have a nonsquare partner for each covered square.
    halves_p, halves_q = (p-1)//2, (q-1)//2
    covered_p, covered_q = local_square_count(p, h), local_square_count(q, h)
    if covered_p != halves_p:
        raise ArithmeticError(f'Public square failed to cover the smaller prime at {n}')
    return Observation(n, p, q, h, a, divisor, gcd_tests, steps,
                       covered_p*halves_q, covered_q*halves_p, 2*halves_p*halves_q)


def target_summary(rows):
    return dict(products=len(rows), first_hits=sum(r.divisor > 1 for r in rows),
                first_misses=sum(r.divisor == 1 for r in rows),
                pooled_hits=sum(r.hits_at_p + r.hits_at_q for r in rows),
                pooled_negative_targets=sum(r.negative_targets for r in rows))


def summary(rows):
    worst = min(rows, key=lambda r: (r.rate, r.n))
    first_misses = [r.n for r in rows if r.divisor == 1]
    rate = sum((r.rate for r in rows), Fraction()) / len(rows)
    grid_only = sum(r.divisor > 1 and r.fermat_steps > 5 for r in rows)
    five_only = sum(r.divisor == 1 and r.fermat_steps <= 5 for r in rows)
    return dict(**target_summary(rows), mean_fixed_product_rate=str(rate),
                minimum_rate=dict(rate=str(worst.rate), product=str(worst.n),
                                  factors=[str(worst.p), str(worst.q)], side=worst.h),
                smallest_first_miss=str(min(first_misses)) if first_misses else None,
                regions={region: target_summary([r for r in rows if r.region == region])
                         for region in ('below_boundary', 'small_deficit', 'beyond_band')},
                first_hits_at_smaller=sum(r.divisor == r.p for r in rows),
                first_hits_at_larger=sum(r.divisor == r.q for r in rows),
                first_target_work=dict(jacobi_tests=sum(r.target-1 for r in rows),
                                       grid_gcds_through_hit_or_exhaustion=sum(r.gcd_tests for r in rows)),
                fermat=dict(one_test_hits=sum(r.fermat_steps == 1 for r in rows),
                            five_test_hits=sum(r.fermat_steps <= 5 for r in rows),
                            midpoint_tests_through_all_splits=sum(r.fermat_steps for r in rows),
                            first_grid_only_vs_five=grid_only, five_only_vs_first_grid=five_only))


def exhaust(row):
    counts = Counter()
    for a in range(row.n):
        if jacobi(a, row.n) == -1:
            divisor, _, _ = nested_gcds(row.n, a, row.h, row.h)
            counts[divisor] += 1
    if (sum(counts.values()), counts[row.p], counts[row.q]) != (
            row.negative_targets, row.hits_at_p, row.hits_at_q) or set(counts) - {1, row.p, row.q}:
        raise ArithmeticError(f'Exhaustive gcd counts disagree with CRT at {row.n}')
    return dict(product=str(row.n), factors=[str(row.p), str(row.q)], side=row.h,
                all_negative_targets=row.negative_targets, gcd_counts=dict(sorted((str(d), k) for d, k in counts.items())),
                uniform_rate=str(row.rate), first_target=row.target, first_grid_gcd=str(row.divisor),
                first_grid_gcd_tests=row.gcd_tests, fermat_midpoint_tests=row.fermat_steps)


def study():
    cohorts = []
    all_rows = []
    for width in range(6, 12):
        rows = [observe(n, p, q) for n, (p, q) in products(width)]
        cohorts.append(dict(factor_bits=width, **summary(rows)))
        all_rows.extend(rows)
    first_miss = min((r for r in all_rows if r.divisor == 1), key=lambda r: r.n)
    lowest = min(all_rows, key=lambda r: (r.rate, r.n))
    first_grid_only = min((r for r in all_rows if r.divisor > 1 and r.fermat_steps > 5), key=lambda r: r.n)
    return dict(cohorts=cohorts, overall=summary(all_rows), exhaustive_examples={
        'smallest_first_miss': exhaust(first_miss), 'minimum_uniform_rate': exhaust(lowest),
        'smallest_grid_hit_after_five_fermat_misses': exhaust(first_grid_only)})


if __name__ == '__main__':
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Public grid target census differs from its fixture')
    overall = result['overall']
    print(f"Checked {overall['products']} products, {overall['first_hits']} first-target hits, "
          f"and three exhaustive target controls.")
