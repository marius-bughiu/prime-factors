from collections import Counter, defaultdict
import json
from math import gcd, prod
from pathlib import Path
import unittest

from experiments.lifted_period_census import compare, survivor_counts
from experiments.lifted_period_holdout import cohort, refined_full_period
from experiments.lifted_period_join import _lifted_table, _prepare, _sweep, search
from experiments.factor_sum_quantile import sum_bounds
from experiments.trace_folded_right import _layers


ROOT = Path(__file__).resolve().parents[1]


class LiftedPeriodJoin(unittest.TestCase):
    def test_exact_lifted_entries_and_keys(self):
        prime, base, lo = 101, 2, 7
        for mods in ((), (3,), (4,), (3, 4), (3, 5)):
            M = prod(mods)
            for cut in range(len(mods) + 1):
                left, right = mods[:cut], mods[cut:]
                # All unit sum menus here are negation-stable, including self-opposite positions.
                menus = {m: {(x + prime * pow(x, -1, m)) % m for x in range(m) if gcd(x, m) == 1}
                         for m in mods}
                power, back = pow(base, M, prime), pow(base, -M, prime)
                groups = [(m, {(s - lo) % m for s in menus[m]}) for m in right]
                _, layers = _layers(groups, M, prime, base, power, back, lo, True, Counter())
                for h in range(1, 7):
                    Q = M * h
                    table = _lifted_table(layers, prime, M, h, power, back, pow(base, Q, prime),
                                          pow(base, -Q, prime), Counter())
                    expect = defaultdict(list)
                    for t in range(Q // 2 + 1):
                        if all(t % m in menus[m] for m in right) and all(t % m == 0 for m in left):
                            expect[(pow(base, t, prime) + pow(base, -t, prime)) % prime].append(t)
                    self.assertEqual({k: sorted(v) for k, v in table.items()}, dict(expect))

    def test_all_compatible_integer_labels_across_many_periods(self):
        n, lo = 101, 21
        mods = [3, 4]
        menus = {m: {(x + n * pow(x, -1, m)) % m for x in range(m) if gcd(x, m) == 1} for m in mods}
        for left, right in (([3], [4]), ([4], [3]), (mods, []), ([], mods)):
            M = prod(mods)
            raw = prod(len(menus[m]) for m in right)
            for h in range(1, 5):
                Q = M * h
                stored = sum(all(t % m in menus[m] for m in right) and all(t % m == 0 for m in left)
                             for t in range(Q // 2 + 1))
                plan = dict(period=M, lift=h, lifted_period=Q, left_moduli=left, right_moduli=right,
                            left_rows=prod(len(menus[m]) for m in left), raw_right=raw,
                            right_entries=stored)
                for base in (1, 2, n - 1):
                    prep = _prepare(n, base, lo, menus, plan, Counter())
                    for a, b in ((0, 0), (0, 125), (21, 114), (53, 199)):
                        work = Counter()
                        status, _ = _sweep(n, base, lo, a, b, plan, prep, True, work)
                        self.assertEqual(status, 'exhausted')  # n is prime
                        allowed = [s for s in range(lo + a, lo + b + 1)
                                   if all(s % m in menus[m] for m in mods)]
                        matches = sum(pow(base, s, n) == pow(base, n + 1, n) for s in allowed)
                        self.assertEqual(work['square_tests'], matches)
                        self.assertLessEqual(work['lookups'], plan['left_rows'] * ((b - a) // Q + 2))
                        counts = survivor_counts(lo + a, {'part': b - a + 1}, menus, plan, 10000)
                        self.assertEqual(int(counts['part']['exact']), len(allowed))

    def test_whole_range_caps_and_limits(self):
        n = 2999205669099453866424720319
        run = search(n)
        self.assertEqual(run['factors'], ['45058864713217', '66561944873407'])
        p, w = run['feasible_plan'], run['work']
        self.assertEqual((p['lift'], p['right_entries'], p['left_rows'], p['lookup_bound']),
                         (5, 17820, 4704, 23520))
        self.assertEqual((w['left_visited'], w['lookups'], w['square_tests']), (765, 3612, 1))
        self.assertLess(p['score'], w['feasible_full_period_reference']['score'])
        stopped = search(n, max_lookups=0)
        self.assertEqual(stopped['outcome'], 'no_complete_plan_within_caps')
        self.assertEqual(stopped['work']['right_built'], 0)
        unplanned = search(n, plan_budget=0)
        self.assertEqual(unplanned['work']['plan_budget_hit'], 1)
        self.assertEqual(unplanned['work']['lift_candidates'], 0)
        self.assertIsNone(unplanned['best_plan'])
        self.assertEqual(search(n, sum_interval=(0, 1))['outcome'], 'empty_interval')
        self.assertEqual(search(33127, candidates=(13,))['outcome'], 'preflight_gcd')

    def test_frozen_census(self):
        pinned = json.loads((ROOT / 'research/lifted-period-census.json').read_text())
        cases = json.loads((ROOT / 'benchmarks/factor-sum-quantile.json').read_text())
        self.assertEqual(len(cases), len(pinned['rows']))
        for case, record in zip(cases, pinned['rows']):
            measured = compare(int(case['n']), case['factor_bits'])
            self.assertEqual(dict(id=case['id'], **measured), record)
        selected = pinned['aggregate']
        totals = [(selected[key]['left_visited'], selected[key]['lookups'])
                  for key in ('full', 'quantile', 'aligned')]
        self.assertEqual(totals, [(3406, 10411), (5071, 10033), (3676, 7193)])
        self.assertEqual(sum(not r['aligned_cut_used'] for r in pinned['rows'] if 'policies' in r), 1)

    def test_first_four_eligible_postdesign_draws(self):
        path = ROOT / 'benchmarks/lifted-period-join.json'
        cases = [row for row in json.loads(path.read_text()) if 'postdesign-96' in row['id']]
        self.assertEqual([row['origin']['sample'] for row in cases], [2, 3, 5, 6])
        self.assertEqual(cohort(), [(row['origin']['sample'], row['n'], row['factors']) for row in cases])
        self.assertTrue(all((row['max_right'], row['max_visited'], row['max_lookups'])
                            == (20000, 32256, 100000) for row in cases))

    def test_refined_full_period_early_hit_with_incomplete_coverage(self):
        n = 44999777202387676883929306237
        lo, _, hi = sum_bounds(n, 48)
        run = refined_full_period(n, lo, hi, 20000, 32256, 100000)
        self.assertEqual(run['wheels'], 67)
        self.assertGreater(run['min_raw_choices'], run['raw_capacity'])
        self.assertEqual((run['left_rows'], run['stored']), (34020, 19800))
        self.assertEqual((run['left_visited'], run['lookups']), (8143, 12449))
        self.assertEqual(run['factors'], ['209966509290409', '214318832819893'])
