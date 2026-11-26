"""Reproduce the 96-bit cohort and compare the complete-period layouts for a single public product."""

from collections import Counter
from itertools import count
from math import gcd, isqrt, prod

from .affine_radix_holdout import draw_prime
from .lifted_period_join import _wheel_options
from .sum_menu_partition import partition
from .sum_signature_join import _moduli
from .trace_folded_right import events


def cohort():
    """The first four eligible products from the fixed SHAKE seed, including their generation labels."""
    selected = []
    for sample in count():
        p, q = sorted(draw_prime(side, sample, bits=48, seed=b'short-period-join-96-postdesign-v1')
                      for side in (b'p', b'q'))
        n = p * q
        if p != q and n.bit_length() == 96:
            selected.append((sample, str(n), [str(p), str(q)]))
            if len(selected) == 4:
                return selected


def refined_full_period(n, lower, upper, max_right, max_visited, max_lookups):
    """Optimize all side assignments at each prescribed full-period wheel, then test one prefix.

    The optimization minimizes the complete left row count. The actual prefix uses
    base 2 and reverse order, testing both square and mixed-trace opportunities.
    """
    width = upper - lower
    if width < 0 or max_right < 1 or min(max_visited, max_lookups) < 0:
        raise ValueError('expected a nonempty interval and a positive storage budget')
    prefix = []
    period = 1
    for m in _moduli():
        if period > width:
            break
        prefix.append(m)
        period *= m

    menus = {}
    best = None
    candidates = 0
    transitions = 0
    min_choices = None
    for _, moduli, _ in _wheel_options(prefix, power_limit=10000, drop_limit=3):
        period = prod(moduli)
        if period <= width:
            continue
        for m in moduli:
            if m not in menus:
                if gcd(n, m) != 1:
                    raise ValueError('comparison requires a product coprime to its wheel')
                menus[m] = {(x + n * pow(x, -1, m) - lower) % m for x in range(m) if gcd(x, m) == 1}
        candidates += 1
        groups = [(m, menus[m]) for m in moduli]
        left, right, plan = partition([groups, []], lower, max_right, folded=True, budget=2_000_000)
        if not plan['optimal']:
            raise ValueError('the best whole-modulus assignment was not established')
        transitions += plan['transitions']
        raw = plan['total_choices']
        min_choices = raw if min_choices is None else min(min_choices, raw)
        criterion = (plan['left_rows'], plan['stored'])
        if best is None or criterion < best[0]:
            best = (criterion, left, right, plan, period)

    _, left, right, plan, period = best
    visit_cap = min(max_visited, max_lookups // 2)
    work = Counter(partition=True, left_unvisited=plan['left_rows'])
    factor = None
    outcome = 'left_limit'
    matches = events(n, 2, lower, width, period, left, right, visit_cap, True, work) if visit_cap else ()
    for total, mixed in matches:
        if mixed is not None:
            outcome, factor = 'trace_mixed_gcd', mixed
            break
        discriminant = total * total - 4 * n
        root = isqrt(discriminant)
        work['square_tests'] += 1
        if root * root == discriminant and (total - root) % 2 == 0:
            divisor = (total - root) // 2
            if 1 < divisor < n and n % divisor == 0:
                outcome, factor = 'sum_square', divisor
                break
    if factor is None and work['left_unvisited'] == 0:
        outcome = 'exhausted'
    return dict(wheels=candidates, transitions=transitions, min_raw_choices=min_choices,
                raw_capacity=2 * max_right * max_visited, left_rows=plan['left_rows'],
                lookup_bound=2 * plan['left_rows'], stored=plan['stored'], right_moduli=plan['right_moduli'],
                period=period, factors=list(map(str, sorted((factor, n // factor)))) if factor else [],
                outcome=outcome, **{k: work[k] for k in ('left_visited', 'left_unvisited', 'right_built',
                                                         'lookups', 'square_tests')})
