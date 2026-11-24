from itertools import combinations
import unittest

from experiments.same_source_pair_bound import probability_bound
from experiments.same_source_pairs import census, minimal_dependencies, pair_witness, short_fractions


class SameSourcePairTests(unittest.TestCase):
    def test_full_size_probability_certificate(self):
        active_primes, exponent = probability_bound()
        self.assertEqual(active_primes, 128)
        self.assertGreater(exponent, 796)

    def test_mixed_ratio_and_original_gcd(self):
        self.assertEqual(pair_witness(437, 104, (-21, 4), (-1, 21)), {
            'reduced_ratio': [2, 21], 'mixed_root': 229, 'left_root': 433,
            'right_root': 42, 'factors': [19, 23],
        })
        self.assertIn((2, 21), short_fractions(437, 229))

    def test_no_pair_and_one_trivial_four_row_dependency(self):
        rows = short_fractions(437, 282)
        self.assertEqual(rows, [(-155, 1), (-28, 3), (15, 14), (2, 31), (-1, 203)])
        self.assertTrue(all(pair_witness(437, 282, *pair) is None
                            for pair in combinations(rows, 2)))
        roots = [x for x in range(437) if x*x % 437 == 282]
        self.assertEqual(minimal_dependencies(437, rows[:4], roots, 4),
                         {'minimal_4_rows_splitting_0_roots': 1})

    def test_higher_order_minimal_dependencies(self):
        for n, r, length, expected in ((143, 126, 4, 4), (247, 225, 3, 2)):
            rows = short_fractions(n, r)[:length]
            roots = [x for x in range(n) if x*x % n == r]
            self.assertEqual(minimal_dependencies(n, rows, roots, length),
                             {f'minimal_{length}_rows_splitting_{expected}_roots': 1})

    def test_exhaustive_small_panel(self):
        panel = census(13, extended=True)
        self.assertEqual(panel['total']['products'], 2)
        self.assertEqual(panel['total']['square_residues'], 6+30)
        self.assertGreater(panel['total']['square_pairs'], 0)
        self.assertLessEqual(panel['total']['realized_ratios'], panel['total']['mixed_chain_ratios'])
