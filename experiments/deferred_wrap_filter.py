"""Measure how often a deferred prime can reject a lifted-join lookup before the hash probe.

Reproduce exact results with
    python3 -m experiments.deferred_wrap_filter | diff - research/deferred-wrap-filter.json
"""

from bisect import bisect_left, bisect_right
from collections import Counter
import json
from math import gcd

from . import lifted_period_join as join
from .factor_sum_quantile import sum_bounds
from .lifted_period_trace import CAPS, ROOT, cases
from .sum_signature_join import _moduli
from .trace_folded_right import _walk


def selected(n, bits):
    lower, _, upper = sum_bounds(n, bits)
    width = upper - lower
    factor, menus, best, feasible = join._plan(n, width, work=Counter(), **CAPS)
    if factor or best is None:
        raise ValueError('expected a coprime input with a public planning result')
    plan = feasible or best
    # The original prime prefix stops at the first product greater than the width.
    original = 1
    deferred = []
    for m in _moduli():
        if original > width:
            break
        original *= m
        if gcd(m, plan['period']) == 1:
            deferred.append(m)
    if not deferred:
        raise ValueError('this panel expects at least one omitted prime')
    return lower, width, menus, plan, deferred, feasible is not None


def prime_menu(n, prime):
    return {(x + n * pow(x, -1, prime)) % prime for x in range(1, prime)}


def check_wrap(positions, origin, lower, upper, largest, menus, counts):
    """Exact local feasibility over all signed positions in the clipped wrap."""
    first = bisect_left(positions, lower - origin)
    stop = bisect_right(positions, upper - origin)
    if first == stop:
        counts['geometry_skips'] += 1
        return
    if first == 0 and stop == len(positions):
        counts['full_range'] += 1
    one_feasible = False
    for i in range(first, stop):
        total = origin + positions[i]
        counts['positions_examined'] += 1
        if total % largest in menus[largest]:
            one_feasible = True
            if all(total % m in values for m, values in menus.items()):
                return
    if not one_feasible:
        counts['single_prime_extra_skips'] += 1
    counts['joint_extra_skips'] += 1


def small_panel(n, bits):
    lower, width, menus, plan, deferred, feasible = selected(n, bits)
    if not feasible:
        raise ValueError('bounded census requires a complete plan')
    work = Counter()
    prepared = join._prepare(n, 2, lower, menus, plan, work)
    left, center, table, start, back, h, inverse_h = prepared
    outcome, factor = join._sweep(n, 2, lower, 0, width, plan, prepared, True, work)
    prefix_lookups = work['lookups']
    lifted = plan['lifted_period']
    positions = sorted(s for bucket in table.values() for t in bucket
                       for s in ((t, -t) if 0 < 2 * t < lifted else (t,)))
    ell = max(deferred)
    filters = {p: prime_menu(n, p) for p in deferred}
    seen = set()
    counters = ('rows', 'lookups', 'duplicate_keys', 'full_range', 'geometry_skips',
                'single_prime_extra_skips', 'joint_extra_skips', 'positions_examined')
    counts = Counter(dict.fromkeys(counters, 0))
    prefix_counts = None
    for a, v, inv in _walk(left, plan['period'], n, start, back, False, True, work):
        counts['rows'] += 1
        first = -((width + lifted // 2 - a - center) // lifted)
        last = (a + center + lifted // 2) // lifted
        for k in range(first, last + 1):
            counts['lookups'] += 1
            key = (v * pow(h, k, n) + inv * pow(inverse_h, k, n)) % n
            counts['duplicate_keys'] += int(key in seen)
            seen.add(key)
            origin = lower + a + center - k * lifted
            check_wrap(positions, origin, lower, lower + width, ell, filters, counts)
            if counts['lookups'] == prefix_lookups:
                prefix_counts = dict(counts)
    return dict(n=str(n), deferred=deferred, largest=ell, menu_size=len(filters[ell]),
                right_projection_size=len({s % ell for s in positions}),
                signed_positions=len(positions), right_keys=len(table),
                outcome=outcome, factors=list(map(str, sorted((factor, n // factor)))) if factor else [],
                complete_schedule=dict(counts), through_stock_stop=prefix_counts)


def wide_subcube(n, bits, bins=256):
    """Exhibit actual right positions in each bin without constructing the right table."""
    _, _, menus, plan, deferred, feasible = selected(n, bits)
    period, lifted = plan['period'], plan['lifted_period']
    ell = max(deferred)
    right = sorted(plan['right_moduli'], key=lambda m: (-len(menus[m]), m))
    m1, m2, *rest = right
    # The visited CRT positions have zero digit on all left moduli, and the
    # minimum allowed sum on each right modulus other than the two varied here.
    weights = {m: period // m * pow(period // m, -1, m) for m in right}
    fixed = sum(weights[m] * min(menus[m]) for m in rest)
    supports = [set() for _ in range(bins)]
    sites = 0
    for a in menus[m1]:
        base = fixed + a * weights[m1]
        for b in menus[m2]:
            residue = (base + b * weights[m2]) % period
            for i in range(plan['lift']):
                s = residue + i * period
                if 2 * s > lifted:
                    s -= lifted
                j = min(bins - 1, (2 * s + lifted) * bins // (2 * lifted))
                supports[j].add(s % ell)
                sites += 1
    smallest = min(map(len, supports))
    menu_size = len(prime_menu(n, ell))
    return dict(n=str(n), plan_fits_caps=feasible, lift=plan['lift'], period=str(period),
                lifted_period=str(lifted), varied_moduli=[m1, m2], deferred=deferred, prime=ell,
                menu_size=menu_size, sites=sites, bins=bins, min_support=smallest,
                factor_search_attempted=False, remaining=[str(n)],
                every_bin_meets_every_translate=smallest + menu_size > ell)


def main():
    small = [dict(id=label, **small_panel(n, bits)) for label, n, bits in cases()]
    rows = json.loads((ROOT / 'benchmarks/factor-sum-quantile.json').read_text())
    controls = {row['id']: row for row in rows}
    wide = [dict(id=label, **wide_subcube(int(controls[label]['n']), 1024))
            for label in ('quantile-fresh-2048', 'quantile-crossed-2048')]
    print(json.dumps(dict(rule='Inspect every signed right position in the clipped wrap until a '
                               'locally allowed sum exists. Extra skips exclude pure geometry skips. '
                               'Large panels instead exhibit a two-digit subcube in 256 equal bins.',
                          caps=CAPS, small=small, wide=wide), indent=2))


if __name__ == '__main__':
    main()
