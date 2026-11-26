from collections import Counter
from itertools import combinations
from math import isqrt
import unittest

from experiments.weighted_pair_hybrid import passing_pairs, run, single_passes


class WeightedPairHybridTests(unittest.TestCase):
    def test_local_filters_preserve_actual_squares_and_zero(self):
        values = [0, 1, 2, 8, 12, 48, 3**5*5**2, 3**7*5**4, 7**2*11**4, 121, 169]
        pairs = passing_pairs([(0, d) for d in values], Counter())
        self.assertEqual(len(pairs), len(set(pairs)))
        for i, j in combinations(range(len(values)), 2):
            d = values[i]*values[j]
            if isqrt(d)**2 == d:
                self.assertIn((i, j), pairs)
        for x in range(200):
            self.assertTrue(single_passes(x*x, Counter()))

    def test_both_strategies_recover_with_different_label_budgets(self):
        n = 137549339
        hybrid = run(n, 'hybrid')
        self.assertEqual((hybrid['divisor'], hybrid['work']['pair_tests']), (8693, 1))
        self.assertEqual(hybrid['ordinary_allowance'], 119)
        self.assertIsNone(run(n, 'ordinary')['divisor'])
        single = run(n, 'sieved_ordinary')
        self.assertEqual((single['divisor'], single['work']['extra_single_tests']), (15823, 2))
        self.assertEqual(single['work']['screened_single_labels'], 130)

    def test_miss_accounts_for_remaining_checks(self):
        n = 908162445584950626852517
        hybrid = run(n, 'hybrid')
        self.assertIsNone(hybrid['divisor'])
        work = hybrid['work']
        self.assertEqual(work['pair_tests'], work['compatible_pairs'])
        self.assertEqual(work['pair_tests'] + work['extra_single_tests'], 120)
        self.assertEqual(work['odd_remainders'], 4*16 + work['odd_unit_divisions'])
        single = run(n, 'sieved_ordinary')
        self.assertIsNone(single['divisor'])
        self.assertTrue(single['work']['extra_single_tests'] == 120 or
                        single['work']['screened_single_labels'] == 4096)
