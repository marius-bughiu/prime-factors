"""Repeat the period-aligned and analytic cuts on the published eight inputs and two controls."""

import argparse
from bisect import bisect_left
from collections import Counter
from decimal import Decimal, localcontext
from itertools import product
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from .factor_sum_quantile import sum_bounds
from .lifted_period_join import _plan, _prepare, _sweep


SEARCH_COSTS = ('right_built', 'left_visited', 'lookups', 'square_tests', 'setup_powers',
                'signature_inversions', 'signature_multiplications')


def survivor_counts(lower, lengths, menus, plan, count_cap):
    """Full periods count exactly; count a bounded remainder by circular interval queries."""
    m = plan['period']
    total = plan['raw_right'] * plan['left_rows']
    counts = {}
    enumerate_tail = max(plan['raw_right'], plan['left_rows']) <= count_cap
    if enumerate_tail:
        def coordinates(moduli):
            digits = []
            for p in moduli:
                cofactor = m // p
                basis = cofactor * pow(cofactor, -1, p)
                digits.append([basis * x % m for x in menus[p]])
            return (sum(xs) % m for xs in product(*digits))

        right = sorted(coordinates(plan['right_moduli']))
        left = list(coordinates(plan['left_moduli']))
    for key, length in lengths.items():
        periods, tail = divmod(length, m)
        exact = periods * total
        if tail and not enumerate_tail:
            counts[key] = dict(lower=str(exact), upper=str(exact + total))
            continue
        if tail:
            for a in left:
                start = (lower - a) % m
                stop = start + tail
                if stop <= m:
                    exact += bisect_left(right, stop) - bisect_left(right, start)
                else:
                    exact += len(right) - bisect_left(right, start) + bisect_left(right, stop - m)
        counts[key] = dict(exact=str(exact))
    return counts


def area_fraction(n, bound, cut):
    """Continuous conditional-area fraction up to the integer sum cutoff."""
    with localcontext() as ctx:
        ctx.prec = 60
        N, S, B = Decimal(n), Decimal(cut), Decimal(bound)
        q = (S + (S * S - 4 * N).sqrt()) / 2
        return str(((q / N.sqrt()).ln() / (B / N.sqrt()).ln()).quantize(Decimal('0.000000000001')))


def compare(n, bits, count_cap=100000):
    lo, central, hi = sum_bounds(n, bits)
    width = hi - lo
    work = Counter()
    factor, menus, best, feasible = _plan(
        n, width, max_right=20_000, max_visited=32_768, max_lookups=100_000,
        power_limit=10_000, drop_limit=3, budget=2_000_000, work=work,
    )
    if factor is not None or best is None:
        raise ValueError('panel expects a complete public planning report')
    plan = feasible or best
    Q = plan['lifted_period']
    nearest = (2 * (central - lo + 1) + Q) // (2 * Q)
    periods = min(width // Q, max(1, nearest))
    cuts = dict(full=hi, quantile=central, aligned=(lo + periods * Q - 1 if periods else hi))
    lengths = {key: end - lo + 1 for key, end in cuts.items()}
    counts = survivor_counts(lo, lengths, menus, plan, count_cap)
    plan_costs = ('local_sites', 'local_inverses', 'wheel_layouts', 'lift_candidates')
    summary = dict(lower=str(lo), upper=str(hi), central=str(central), aligned=str(cuts['aligned']),
                   periods=periods, aligned_cut_used=bool(periods), lifted_period=str(Q),
                   first_interval_lengths={key: str(length) for key, length in lengths.items()},
                   planning={key: work[key] for key in plan_costs},
                   aligned_area_fraction=area_fraction(n, 1 << bits, cuts['aligned']),
                   local_menu_counts=counts, estimated_score=plan['score'],
                   right_entries=plan['right_entries'])
    max_rows = 2 * plan['left_rows']
    max_lookups = plan['lookup_bound'] + plan['left_rows']
    if not feasible or max_rows > 32_768 or max_lookups > 100_000:
        return summary
    policies = {}
    for policy, end in cuts.items():
        costs = Counter()
        prepared = _prepare(n, 2, lo, menus, plan, costs)
        status, factor = _sweep(n, 2, lo, 0, end - lo, plan, prepared, reverse=True, work=costs)
        first = factor is not None
        if not first and end < hi:
            status, factor = _sweep(n, 2, lo, end + 1 - lo, width, plan, prepared,
                                    reverse=True, work=costs)
        if costs['lookups'] > max_lookups or costs['left_visited'] > max_rows:
            raise ArithmeticError('two-part work bound exceeded')
        factors = list(map(str, sorted((factor, n // factor)))) if factor else []
        policies[policy] = dict(status=status, factors=factors, first=first,
                                **{key: costs[key] for key in SEARCH_COSTS})
    summary['policies'] = policies
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--verify', action='store_true',
                        help='generate and kernel-check each recovered factorization')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    evidence = []
    for row in json.loads((root / 'benchmarks/factor-sum-quantile.json').read_text()):
        # Labels enter only after the policies finish on the product.
        report = compare(int(row['n']), row['factor_bits'])
        if 'policies' in report:
            for result in report['policies'].values():
                if result['factors'] != row['factors']:
                    raise ArithmeticError('split disagrees with the certified panel')
            if args.verify:
                from scripts.factor import render_certificate, verify_file

                with TemporaryDirectory() as directory:
                    proof = Path(directory) / 'Certificate.lean'
                    factors = list(map(int, report['policies']['full']['factors']))
                    source = render_certificate(int(row['n']), factors, certificate_trial_limit=1_000_000)
                    proof.write_text(source)
                    verify_file(proof)
        evidence.append(dict(id=row['id'], **report))
    measured = [row['policies'] for row in evidence if 'policies' in row]
    costs = ('right_built', 'left_visited', 'lookups', 'square_tests', 'signature_multiplications',
             'setup_powers', 'signature_inversions')
    aggregate = {}
    for key in ('full', 'quantile', 'aligned'):
        total_costs = {metric: sum(run[key][metric] for run in measured) for metric in costs}
        aggregate[key] = dict(first_piece=sum(run[key]['first'] for run in measured),
                              complete=sum(bool(run[key]['factors']) for run in measured),
                              **total_costs)
    result = dict(source='benchmarks/factor-sum-quantile.json',
                  rule=('The full-interval plan supplies Q. Choose the nearest positive multiple '
                        'of Q to the central prefix length that leaves a nonempty suffix; '
                        'if none exists search the full interval once.'),
                  caps=dict(max_right=20000, max_total_visits=32768, max_total_lookups=100000),
                  aggregate=aggregate, rows=evidence)
    rendered = json.dumps(result, indent=2) + '\n'
    if args.out:
        args.out.write_text(rendered)
    else:
        print(rendered, end='')


if __name__ == '__main__':
    main()
