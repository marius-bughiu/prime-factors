import unittest
from collections import Counter
from math import gcd

from experiments.affine_radix_holdout import trial_search
from experiments.midpoint_weights import possible_x, residue_pairs, search, weight_interval


class MidpointWeightsTests(unittest.TestCase):
    def test_complete_balanced_pairs(self):
        # Includes empty intervals, squares, multiple balanced pairs and shared small primes.
        for n in range(3, 5000, 2):
            result = search(n)
            self.assertEqual(result['pairs'], trial_search(n)['pairs'], n)
            self.assertEqual(search(n, reduce_discriminant=True)['pairs'], result['pairs'])
            self.assertEqual(result['remaining_orbits'], 0)
            self.assertLessEqual(result['candidate_traces'], result['visited_orbits'])

    def test_crt_swap_orbits_include_fixed_points(self):
        for radix in range(2, 45):
            for n in (1, 3, 35, 77, 121):
                if gcd(n, radix) != 1:
                    continue
                target = {tuple(sorted((u, n*pow(u, -1, radix) % radix)))
                          for u in range(radix) if gcd(u, radix) == 1}
                total, pairs = residue_pairs(n, radix, Counter())
                actual = [tuple(sorted(pair)) for pair in pairs]
                self.assertEqual(len(actual), total)
                self.assertCountEqual(actual, target)

    def test_minimum_certified_width(self):
        for radix in range(6, 24):
            for slope in range(radix):
                for h, gap in ((1, 2), (3, 5), (1, 15)):
                    a, b, left, right = weight_interval(radix, slope, 4, 4+h, gap, Counter())
                    width = right-left
                    self.assertEqual(width, h*abs(a+b)+2*gap*abs(a-b))
                    # A smaller pair must satisfy |a|, |b| <= width when h, 2*gap >= 1.
                    better = any(h*abs(x+y)+2*gap*abs(x-y) < width
                                 for x in range(-width, width+1)
                                 for y in range(-width, width+1)
                                 if (x or y) and (y-slope*x) % radix == 0)
                    self.assertFalse(better)

    def test_quadratic_and_linear_roots(self):
        for x, y in ((7, 11), (7, 7)):
            for a, b in ((0, -2), (3, 0), (1, -1), (-3, -2), (1, 1)):
                self.assertIn(x, possible_x(x*y, a, b, a*y+b*x, Counter()))

    def test_small_and_truncated_runs(self):
        self.assertEqual(search(9, 0)['remaining_orbits'], 1)
        self.assertEqual(search(34387, 0)['visited_orbits'], 0)
        self.assertEqual(search(34387, 1)['remaining_orbits'], 3)
        with self.assertRaises(ValueError):
            search(34387, -1)
