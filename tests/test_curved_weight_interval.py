import unittest

from experiments.curved_weight_interval import curved_interval


class CurvedWeightTests(unittest.TestCase):
    def test_signed_extrema_tangency_and_empty_intersection(self):
        for a, b, expected in [(5,-3,(-2,14)), (-5,3,(-14,2)), (1,-1,(-2,2)), (0,0,(0,0))]:
            self.assertEqual(curved_interval(8, a, b, -100, 100), expected)
        self.assertEqual(curved_interval(77, 11, 7, 0, 999)[0], 154)
        self.assertEqual(curved_interval(77, -11, -7, -999, 0)[1], -154)
        self.assertEqual(curved_interval(8, 5, -3, 15, 20), (15, 14))
        self.assertEqual(curved_interval(7, 5, -3, -100, 100), (-1, 13))

    def test_all_balanced_integer_factor_pairs_survive(self):
        for p in range(1, 42, 2):
            for q in range(p, 2*p+1, 2):
                for a in range(-5, 6):
                    for b in range(-5, 6):
                        low, high = curved_interval(p*q, a, b, -10000, 10000)
                        for t in (a*p+b*q, a*q+b*p):
                            self.assertLessEqual(low, t)
                            self.assertLessEqual(t, high)
