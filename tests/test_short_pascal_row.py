import unittest
from itertools import combinations
from math import comb, gcd, isqrt

from experiments.factorial_progressions import search as progression
from experiments.short_pascal_row import interval, search


class ShortRowTests(unittest.TestCase):
    def test_all_columns_and_equal_width_bounds(self):
        primes = [p for p in range(3, 128, 2) if all(p%d for d in range(3, isqrt(p)+1, 2))]
        for p, q in combinations(primes, 2):
            if p.bit_length() != q.bit_length():
                continue
            n = p*q
            lower, u = interval(n)
            self.assertLessEqual(lower, p)
            self.assertGreaterEqual(lower, isqrt((n-1)//2)+1)
            self.assertEqual(search(n, u)[0], p)
            for k in range(u+1):
                self.assertEqual(gcd(comb(u,k), n)==p, u-p<k<p)
            self.assertEqual(progression(n, None, wheel=30, equal_width=True)['factor'], p)

    def test_short_row_does_not_evaluate_above_budget(self):
        n = 2028838549
        self.assertEqual(interval(n), (32768,45042))
        factor, work = search(n, 12274)
        self.assertIsNone(factor)
        self.assertEqual((work['coefficients_evaluated'], work['residue']), (0,None))
        factor, work = search(n, 12275)
        self.assertEqual((factor, work['coefficient_bits']), (32993,38056))
