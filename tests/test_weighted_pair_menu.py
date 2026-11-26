import unittest
from itertools import combinations
from math import gcd, isqrt

from experiments.weighted_pair_menu import compare


class WeightedPairMenuTests(unittest.TestCase):
    def test_different_weights_add_to_initial_labels(self):
        result = compare(630761)
        self.assertIsNone(result['initial'])
        self.assertEqual(result['extra_single'], '619')
        self.assertEqual(result['cross_weight_nonsquare_pair'], dict(
            rows=[[2, 1], [6, 0]], labels=['2249', '3891'],
            excesses=['11913', '1617'], square_root='4389', divisor='619'))

    def test_within_weight_pair_survives_matched_comparison(self):
        result = compare(136036757)
        self.assertIsNone(result['initial'])
        self.assertIsNone(result['extra_single'])
        self.assertIsNone(result['cross_weight_nonsquare_pair'])
        self.assertEqual(result['pair']['rows'], [[5, 0], [5, 1]])
        self.assertEqual(result['pair']['divisor'], '8693')

    def test_charges_every_square_including_trivial_gcd(self):
        n = 77
        rows = []
        extra = []
        for weight in range(1, 9):
            stride = gcd(24, 2*(weight+n))
            label = isqrt(4*weight*n-1)+1
            while (label-weight-n) % stride:
                label += 1
            labels = [(t, t*t-4*weight*n) for t in range(label, label+17*stride, stride)]
            rows.extend(labels[:2])
            extra.extend(labels[2:])
        work = compare(n)['work']
        self.assertEqual((work['initial_tests'], work['extra_single_tests'], work['pair_tests']),
                         (len(rows), len(extra), len(list(combinations(rows, 2)))))
        self.assertEqual(work['initial_gcds'], sum(isqrt(d)**2 == d for _, d in rows))
        self.assertEqual(work['extra_single_gcds'], sum(isqrt(d)**2 == d for _, d in extra))
        gcds = [gcd(n, a*b-isqrt(d*e)) for (a, d), (b, e) in combinations(rows, 2)
                if isqrt(d*e)**2 == d*e]
        self.assertIn(n, gcds)
        self.assertEqual((work['pair_gcds'], work['proper_pair_gcds']),
                         (len(gcds), sum(1 < g < n for g in gcds)))
