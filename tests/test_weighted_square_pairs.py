import json
import unittest
from pathlib import Path
from math import gcd, isqrt

from experiments.weighted_square_pairs import census, first_label, row_factor, search


class WeightedSquarePairTests(unittest.TestCase):
    def test_two_failed_rows_split_and_matched_alternative(self):
        n = 559697
        result = search(n)
        self.assertEqual(result['factor'], 887)
        self.assertEqual(result['root'], '10968')
        for w in (1, 2):
            label, step = first_label(n, w)
            self.assertIsNone(row_factor(n, label, label*label - 4*w*n))
        a, step = first_label(n, 1)
        self.assertEqual(row_factor(n, a+step, (a+step)**2-4*n), 631)

    def test_planted_ratio_and_separate_product_only_search(self):
        case = json.loads((Path(__file__).resolve().parents[1] /
                           'research/weighted-pair-control.json').read_text())
        n = int(case['n'])
        p, q = map(int, case['expected_factors'])
        self.assertEqual(n.bit_length(), 2048)
        run = search(n)
        self.assertEqual(run['factor'], q)
        self.assertTrue(all(isqrt(d)**2 != d for d in map(int, run['excesses'])))
        # 1/r = (137 + 48 sqrt(2))/289. The ratio-informed baseline gets one guess.
        guess = 1 + isqrt((137*n + isqrt(4608*n*n))//289)
        self.assertEqual(guess, p)
        scaled = 137*p-49*q
        self.assertGreater(scaled, 49)
        self.assertLess((scaled-49)**2, 4608*p*p)
        self.assertLess(4608*p*p, scaled**2)
        for w in (1, 2):
            a, step = first_label(n, w)
            self.assertIsNone(row_factor(n, a+step, (a+step)**2-4*w*n))
        self.assertEqual(p*q, n)

    def test_minimal_labels_and_no_false_factor(self):
        for n in range(5, 1600):
            if gcd(n, 6) != 1:
                continue
            for w in (1, 2):
                a, step = first_label(n, w)
                self.assertEqual((a-w-n) % step, 0)
                self.assertGreaterEqual(a*a, 4*w*n)
                self.assertLess(a-step, 1+isqrt(4*w*n-1))
            f = search(n)['factor']
            if f is not None:
                self.assertTrue(1 < f < n and n % f == 0)

    def test_small_complete_population(self):
        self.assertEqual(census(10)['additional_cross'], 1)
        self.assertEqual(census(10)['eligible'], 1718)
