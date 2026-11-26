from collections import Counter
from itertools import combinations, islice, product
from math import gcd, isqrt, prod
import unittest

from experiments.streamed_sum_join import _digits, _plan_crt, _rows, search
from experiments.sum_menu_partition import partition, prefix_sizes
from experiments.trace_folded_right import events, orbit_count


class SumMenuPartition(unittest.TestCase):
    def test_optimal_against_all_assignments_including_fixed_points(self):
        for n, lower in ((1, 0), (7, 5), (17, 12), (31, 23)):
            groups = [(m, {(x+n*pow(x, -1, m)-lower) % m
                           for x in range(1,m) if gcd(x,m) == 1}) for m in (4,3,5,7,11,13)]
            for folded in (False, True):
                possible = []
                for size in range(len(groups)+1):
                    for subset in combinations(groups, size):
                        raw = prod(len(menu) for _, menu in subset)
                        stored = orbit_count(subset, lower, raw)[0] if folded else raw
                        possible.append((raw, stored))
                for cap in (1, 2, 3, 5, 7, 16, 25, 50, 10000):
                    left, right, plan = partition([groups[::2], groups[1::2]], lower, cap, folded, 10000)
                    self.assertTrue(plan['optimal'])
                    self.assertLessEqual(plan['stored'], cap)
                    self.assertEqual(plan['right_choices'], max(raw for raw, s in possible if s<=cap))
                    self.assertEqual(plan['right_choices'], prod(len(v) for _,v in right))
                    self.assertEqual(plan['left_rows'], prod(len(v) for _,v in left))
                    self.assertEqual(plan['total_choices'], plan['left_rows']*plan['right_choices'])

    def test_fallback_respects_strict_transition_and_storage_caps(self):
        groups = [(m, set(range(m))) for m in (2, 3, 5, 7, 11, 13)]
        for budget in (0, 1, 3):
            _, _, plan = partition([groups[::2], groups[1::2]], 0, 24, True, budget)
            self.assertFalse(plan['optimal'])
            self.assertEqual(plan['outcome'], 'budget')
            self.assertEqual(plan['transitions'], budget)
            self.assertLessEqual(plan['peak_states'], budget+1)
            self.assertLessEqual(plan['stored'], 24)
        _, _, no_table = partition([groups, []], 0, 0, True, 0)
        self.assertEqual(no_table['outcome'], 'no_feasible_table')
        self.assertEqual(no_table['stored'], 1)

    def test_cartesian_prefix_clipping_both_orders(self):
        for sizes in ([], [1], [2,3,5], [2,1,3,4], [5,2,3]):
            for reverse in (False, True):
                axes = [list(range(s))[::-1 if reverse else 1] for s in sizes]
                original = list(product(*axes))
                for cap in range(len(original)+3):
                    needed = prefix_sizes(sizes, cap)
                    limited = product(*(axis[:count] for axis,count in zip(axes,needed)))
                    self.assertEqual(list(islice(limited,cap)), original[:cap])

    def test_capped_left_digits_preserve_exact_row_and_signature(self):
        n, lower, width, g = 1759, 84, 360, 7
        _, period, halves, _ = _plan_crt(n, lower, width, Counter())
        left, right, _ = partition(halves, lower, 2, True, 1000)
        for reverse in (False, True):
            inverse_period = pow(g,-period,n)
            for limit in (1, 2, 3, 5):
                complete = _digits(left,period,n,g,inverse_period,True,Counter())
                small = _digits(left,period,n,g,inverse_period,True,Counter(),limit,reverse)
                start = pow(g, n+1-lower, n)
                suffix = (period, n, start, Counter(), reverse)
                self.assertEqual(list(islice(_rows(complete,*suffix),limit)),
                                 list(islice(_rows(small,*suffix),limit)))
                for base in (1, n-1, g):
                    data = (n,base,lower,width,period,left,right,limit,reverse)
                    complete_events = list(events(*data,Counter()))
                    clipped_events = list(events(*data,Counter(partition=1)))
                    self.assertEqual(complete_events, clipped_events)

    def test_complete_rows_cover_small_balanced_true_sums(self):
        primes = (43, 47, 53, 59, 61, 67, 71, 73, 79, 83)
        for p,q in combinations(primes,2):
            for folded in (False,True):
                n = p*q
                # A proper gcd may also resolve the input during preflight.
                run = search(n, candidates=(2,3,5,7,11), max_right=2, max_visited=1000,
                             folded=folded, memory_partition=True)
                self.assertEqual(run['factors'], [str(p),str(q)])
                if 'partition' in run['work']:
                    w = run['work']
                    self.assertLessEqual(w['right_built'], 2)
                    self.assertLessEqual(w['left_visited'], w['partition']['left_rows'])

    def test_sum_subintervals_are_inclusive_and_empty_means_no_work(self):
        p,q = 449,829
        n = p*q
        lower = isqrt(4*n-1)+1
        upper = isqrt(9*n//2)
        for requested in ((0, lower-1), (upper+1,upper+10), (p+q+1,p+q)):
            run = search(n, sum_interval=requested, folded=True, memory_partition=True)
            self.assertEqual(run['outcome'], 'empty_interval')
            w = run['work']
            self.assertGreater(w['lower'], w['upper'])
            self.assertEqual((w['width'], w['preflight_gcds'], w['local_moduli']), (0,0,0))
        run = search(n, candidates=(5,), sum_interval=(p+q,p+q), memory_partition=True, folded=True)
        self.assertEqual(run['factors'], [str(p),str(q)])
        w = run['work']
        self.assertEqual((w['lower'],w['upper'],w['width']), (p+q,p+q,0))
        with self.assertRaises(ValueError):
            search(n, sum_interval=(1.5,upper))
