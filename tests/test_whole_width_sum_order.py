import unittest

from experiments.whole_width_sum_order import census


class WholeWidthSumOrderTests(unittest.TestCase):
    def test_first_positive_width(self):
        self.assertEqual([census(b)['groups']['pooled']['saved_tests']
                          for b in range(2, 9)], [0, 0, 0, 0, 0, 1, 1])

    def test_complete_twelve_bit_population_and_two_direct_controls(self):
        row = census(12)
        pooled = row['groups']['pooled']
        self.assertEqual((row['full_width_pairs'], pooled['pairs']), (19546, 9744))
        self.assertEqual((pooled['ascending_tests'], pooled['prioritized_tests']),
                         (46345, 43118))
        self.assertEqual(row['groups']['equal']['saved_tests'], 14330)
        self.assertEqual(row['groups']['opposite']['saved_tests'], -11103)
        for group, n, factors, base, priority in [
            ('equal', '8402929', ['2053', '4093'], 24, 7),
            ('opposite', '8488399', ['2081', '4079'], 24, 25),
        ]:
            with self.subTest(group=group):
                measured = row['examples'][group]
                self.assertEqual(measured['n'], n)
                self.assertEqual(measured['factors'], factors)
                self.assertEqual((measured['ascending_tests'], measured['prioritized_tests']),
                                 (base, priority))
