import unittest
from math import comb, factorial

from experiments.binomial_divisor_window import cleared_basis, search
from experiments.quartic_divisor_window import evaluate


class CenteredBinomialWindowTests(unittest.TestCase):
    def test_signed_coordinate_maximum_including_degree_larger_than_radius(self):
        degree = 6
        for radius in (3, 4, 9):
            for i, row in enumerate(cleared_basis(degree)):
                values = [abs(evaluate(row, x)) for x in range(-radius, radius + 1)]
                weight = comb(radius + i - 1, i) if i else 1
                self.assertEqual(max(values), weight * factorial(degree))
                self.assertEqual(values[0], max(values))

    def test_short_rows_find_all_divisors_including_endpoints(self):
        for n, first, span in ((143, 9, 4), (143, 11, 4), (221, 9, 4), (132079, 269, 16)):
            w = search(n, first, span, degree=4, depth=2, centered=True)
            self.assertTrue(w['short'])
            self.assertEqual((w['origin'], w['upper'], w['progression_size']),
                             (first + span, first + 2 * span, span + 1))
            self.assertEqual(w['divisors'], [x for x in range(first, w['upper'] + 1, 2) if n % x == 0])

    def test_mode_and_denominator_precheck(self):
        ordinary = search(15, 27, 9, degree=5, depth=2)
        self.assertNotIn('centered', ordinary)
        with self.assertRaises(ValueError):
            search(143, 9, 5, degree=4, depth=2, centered=True)
        w = search(15, 27, 8, degree=5, depth=2, centered=True)
        self.assertEqual(w['origin'], 35)
        self.assertGreater(w['denominator_factor'], 1)
        self.assertFalse(w['excluded'])
