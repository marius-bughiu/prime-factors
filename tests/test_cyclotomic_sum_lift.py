import unittest

from experiments.cyclotomic_sum_lift import comparisons, search


class CyclotomicSumLift(unittest.TestCase):
    def test_zero_cap_preserves_the_proven_sum_lane(self):
        d, work = search(4193821, 0)
        self.assertIsNone(d)
        self.assertEqual(work['outcome'], 'test_cap')
        self.assertEqual((work['sum_residue'], work['sum_modulus']), (22, 25))
        self.assertEqual((work['eligible'], work['unvisited']), (5, 5))

    def test_positive_and_matched_control(self):
        self.assertEqual(search(4193821, 5)[0], 1471)
        d, work = search(4201121, 5)
        self.assertIsNone(d)
        self.assertEqual((work['outcome'], work['square_tests']), ('no_order_witness', 0))
        runs = comparisons(4193821, 150)
        self.assertEqual(runs['ordinary']['square_tests'], 32)
        self.assertEqual(runs['trial']['divisor_tests'], 3)
