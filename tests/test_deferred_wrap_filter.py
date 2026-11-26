from collections import Counter
import unittest

from experiments.deferred_wrap_filter import check_wrap, prime_menu, small_panel, wide_subcube
from experiments.lifted_period_trace import FRESH_N


class DeferredWrapFilterTests(unittest.TestCase):
    def test_exact_single_and_joint_skips_on_tiny_wraps(self):
        positions = [-9, -4, -2, 0, 2, 4, 9]
        filters = {m: prime_menu(187, m) for m in (5, 7)}
        for origin in range(20, 55):
            for lower, upper in ((22, 22), (25, 28), (30, 46)):
                cost = Counter()
                check_wrap(positions, origin, lower, upper, 7, filters, cost)
                sums = [origin + t for t in positions if lower <= origin + t <= upper]
                single = any(s % 7 in filters[7] for s in sums)
                joint = any(all(s % m in menu for m, menu in filters.items()) for s in sums)
                self.assertEqual(cost['geometry_skips'], int(not sums))
                self.assertEqual(cost['single_prime_extra_skips'], int(bool(sums) and not single))
                self.assertEqual(cost['joint_extra_skips'], int(bool(sums) and not joint))

    def test_fresh_schedule_full_cost_and_boundaries(self):
        row = small_panel(FRESH_N, 46)
        cost = row['complete_schedule']
        self.assertEqual(row['right_projection_size'], 37)
        self.assertEqual(cost['lookups'], 13_449)
        self.assertEqual(cost['geometry_skips'], 1)
        self.assertEqual(cost['single_prime_extra_skips'], 0)
        self.assertEqual(cost['duplicate_keys'], 0)

    def test_two_digit_subcube_pigeonhole_on_small_plan(self):
        row = wide_subcube(FRESH_N, 46, bins=2)
        self.assertTrue(row['every_bin_meets_every_translate'])
        self.assertGreater(row['min_support'] + row['menu_size'], row['prime'])
