import itertools
import json
from math import isqrt, prod
from pathlib import Path
import unittest

from experiments.offset_crt_reconstruction import local_slopes, search
from experiments.offset_crt_wheel import cheapest_subset, choose_wheel
from scripts.factor import primes_through


ROOT = Path(__file__).resolve().parents[1]


def sides(n):
    t = isqrt(n)
    h = n - t*t
    j = isqrt(4*h // 3)
    return j, t*j // h + 1


class CRTWheelTests(unittest.TestCase):
    def test_exact_menu_optimum_uses_strict_threshold(self):
        primes = (3, 5, 7, 11, 13)
        counts = {p: len(local_slopes(p, 101, 10)) for p in primes}
        subsets = [s for n in range(len(primes)+1) for s in itertools.combinations(primes, n)]
        thresholds = {0, 1, 7, 31, 100, prod(primes)-1}
        thresholds.update(prod(s) for s in subsets if s != primes)
        for target in thresholds:
            feasible = [(prod(counts[p] for p in s), prod(s)) for s in subsets if prod(s) > target]
            chosen, cost, modulus, work = cheapest_subset(primes, counts, target)
            self.assertEqual((cost, modulus), min(feasible))
            self.assertEqual(prod(chosen), modulus)
            self.assertEqual(work['threshold_queries'], work['left_subsets'])
        with self.assertRaises(ValueError):
            cheapest_subset(primes, counts, prod(primes))

    def test_counts_match_enumerated_slope_sets_and_actual_selected_wheel(self):
        expected = [(117449, 672, 168), (9017, 90, 54), (50629, 672, 112)]
        for n, baseline, selected in expected:
            j, k = sides(n)
            plan = choose_wheel(n, j, k)
            self.assertIsNone(plan['factor'])
            self.assertEqual(plan['baseline_tuples'], baseline)
            self.assertEqual(plan['total_tuples'], selected)
            self.assertEqual(prod(plan['primes']), plan['modulus'])
            self.assertGreater(plan['modulus'], 2*j*k)
            self.assertEqual(len(set(plan['primes'])), len(plan['primes']))
            self.assertEqual(prod(len(local_slopes(p, n, isqrt(n))) for p in plan['primes']), selected)
            self.assertEqual(plan['work']['trial_divisions'], plan['work']['euler_tests'])

    def test_small_global_optima_against_all_primes_that_can_beat_the_incumbent(self):
        for n in (117449, 9017, 50629):
            j, k = sides(n)
            plan = choose_wheel(n, j, k, prove_bound=True)
            limit, goal = plan['total_tuples'], 2*j*k
            # A prime above 2*limit has more local labels than the entire incumbent.
            pool = [p for p in primes_through(2*limit) if p >= 3 and n % p]
            costs = [len(local_slopes(p, n, isqrt(n))) for p in pool]

            def optimum(start, modulus, count):
                if modulus > goal:
                    return count
                best = limit
                for index in range(start, len(pool)):
                    next_count = count * costs[index]
                    if next_count > limit:
                        break
                    best = min(best, optimum(index+1, modulus*pool[index], next_count))
                return best

            self.assertTrue(plan['global_bound']['globally_optimal'])
            self.assertEqual(optimum(0, 1, 1), plan['global_bound']['lower'])

    def test_trial_divisor_in_lookahead_is_reported_separately(self):
        n = 13*17
        plan = choose_wheel(n, *sides(n))
        self.assertEqual(plan['factor'], 13)
        self.assertEqual(plan['primes'], ())
        self.assertIsNone(plan['total_tuples'])
        self.assertEqual(plan['work']['euler_tests'], 0)
        self.assertEqual(plan['work']['trial_divisions'], 5)
        prime_input = choose_wheel(17, 1, 2)
        self.assertIsNone(prime_input['factor'])
        self.assertNotIn(17, prime_input['free'])

    def test_full_size_compares_against_ascending_without_enumeration(self):
        cases = json.loads((ROOT/'benchmarks/grouped-norm.json').read_text())
        for case in cases:
            if case['id'] not in ('grouped-norm-fresh-2048', 'grouped-norm-crossed-2048'):
                continue
            n = int(case['n'])
            plan = choose_wheel(n, *sides(n), prove_bound=True)
            lower = plan['global_bound']['lower']
            self.assertLessEqual(lower, plan['total_tuples'])
            self.assertGreater(lower, 2**897)
            self.assertGreater(273*lower, 100*plan['total_tuples'])
            self.assertGreater(plan['modulus'], plan['threshold'])
            self.assertLessEqual(plan['total_tuples'], plan['baseline_tuples'])
            self.assertTrue(set(plan['fixed']).issubset(plan['primes']))
            self.assertTrue(set(plan['primes']).issubset(set(plan['fixed']) | set(plan['free'])))
            self.assertLessEqual(len(plan['free']), 25)
            self.assertEqual(plan['work']['left_subsets'] + plan['work']['right_subsets'], 12288)

    def test_complete_search_on_same_public_inputs(self):
        for n in (117449, 9017):
            direct = search(n, 1000, exhaust=True)
            selected = search(n, 1000, exhaust=True, optimize_wheel=True)
            self.assertEqual(selected['proper_hits'], direct['proper_hits'])
            self.assertEqual({selected['factor'], selected['remaining']}, {direct['factor'], direct['remaining']})
            self.assertEqual(selected['unchecked_tuples'], 0)
            self.assertLess(selected['visited_tuples'], direct['visited_tuples'])
            capped = search(n, 2, optimize_wheel=True)
            self.assertEqual(capped['visited_tuples'], 2)
            self.assertEqual(capped['unchecked_tuples'], capped['total_tuples'] - 2)
