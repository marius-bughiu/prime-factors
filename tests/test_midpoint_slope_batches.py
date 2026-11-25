import unittest
from collections import Counter
from itertools import product
from math import gcd, isqrt
from random import Random

from experiments.midpoint_slope_batches import joined_traces, local_slope_tables, search
from experiments.midpoint_weights import residue_pairs


class MidpointSlopeBatchTests(unittest.TestCase):
    def test_all_balanced_pairs_including_squares_and_repeated_factors(self):
        for n in range(3, 3001, 2):
            expected = [[str(x), str(n//x)] for x in range(2, isqrt(n)+1)
                        if n % x == 0 and n//x <= 2*x]
            for multiplier in (1, 2, 3):
                if gcd(n, multiplier) == 1:
                    result = search(n, multiplier=multiplier)
                    self.assertEqual(result['pairs'], expected)
                    self.assertEqual(result['outcome'], 'complete')
                    self.assertEqual(result['remaining_orbits'], 0)

    def test_canonical_slope_count_equals_the_full_image(self):
        for radix in range(2, 80):
            for n in (1, 3, 35, 77, 121):
                if gcd(radix, n) != 1:
                    continue
                tables, _, count = local_slope_tables(n, radix, Counter())
                full = {sum(row[0] for row in config) % radix for config in product(*tables)}
                total, pairs = residue_pairs(n, radix, Counter())
                self.assertEqual(full, {w*pow(u, -1, radix) % radix for u, w in pairs})
                self.assertEqual(count, total)

    def test_two_bisected_windows_report_exact_sums(self):
        rng = Random(73793)
        for step in (3, 20, 277):
            for _ in range(80):
                a = rng.sample(range(step), rng.randint(1, min(4, step)))
                b = rng.sample(range(step), rng.randint(1, min(4, step)))
                offset, left = rng.randrange(3*step), rng.randrange(-3*step, 3*step)
                right = left+rng.randrange(step)
                actual = joined_traces(([a], [b]), offset, left, right, step)
                full = [left+(x+y+offset-left) % step for x in a for y in b]
                self.assertCountEqual(actual, [x for x in full if x <= right])

    def test_limits_leave_unprocessed_slopes_and_orbits_visible(self):
        n = 502005281288939
        for extra, outcome in ((dict(max_slopes=1), 'slope_limit'),
                               (dict(max_half_entries=0), 'half_list_limit')):
            result = search(n, **extra)
            self.assertEqual(result['outcome'], outcome)
            self.assertGreater(result['remaining_slopes'], 0)
            self.assertGreater(result['remaining_orbits'], 0)
            self.assertEqual(result['total_slopes'], result['remaining_slopes']+result['visited_slopes'])
        for extra in (dict(multiplier=0), dict(max_slopes=-1), dict(max_half_entries=-1)):
            with self.assertRaises(ValueError):
                search(n, **extra)
