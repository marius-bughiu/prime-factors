import unittest

from experiments.primitive_multiplier_traces import SCHEDULES, compare


class PrimitiveMultiplierTests(unittest.TestCase):
    def test_all_square_roots_and_factors_agree(self):
        # Include a repeated prime, shared prime scales, and a product with three factors.
        for n in (25, 35, 77, 105, 143, 385):
            for mode in (SCHEDULES if n % 3 else ('raw',)):
                run = compare(n, 64, 12, mode)
                self.assertGreater(run['reduced']['contracted'], 0)
                self.assertGreater(run['squares'], 0)
                self.assertEqual(run['reduced']['hit_gcds'], 2*run['squares'])

    def test_zero_height_and_nonunit_wheel(self):
        for mode in SCHEDULES:
            self.assertEqual(compare(77, 4, 0, mode)['reduced']['square_tests'], 0)
        with self.assertRaises(ValueError):
            compare(21, 4, 2, 'wheel-prefix')

    def test_uniform_bound_at_both_parities(self):
        for lanes in (7, 8, 9):
            for height in (7, 8, 9):
                run = compare(143, lanes, height, 'raw')
                self.assertGreaterEqual(run['reduced']['contracted'], (lanes//4)*(height//2))

    def test_filtered_bound_for_each_product_residue(self):
        for n in (25, 29, 31, 35, 37, 41, 43, 47):
            for height in (12, 13, 14, 26):
                run = compare(n, 32, height, 'wheel-prefix')
                self.assertGreaterEqual(run['reduced']['contracted'], 8*(height//13))
