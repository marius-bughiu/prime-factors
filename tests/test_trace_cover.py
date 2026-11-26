from fractions import Fraction
from itertools import product
from math import gcd
from unittest import TestCase

from experiments.trace_cover import cover_cost, envelope, solve, two_slopes, verify


class TraceCoverTests(TestCase):
    def test_certified_minimum_agrees_with_exhaustion(self):
        for n in (25, 35, 77, 143, 2537, 10403, 34387):
            for k, block in ((1, 1), (2, 2), (3, 3)):
                result = solve(n, k, block)
                windows, optimum = result['windows'], result['optimum']
                for budgets in product(range(optimum), repeat=len(windows)):
                    if sum(budgets) >= optimum:
                        continue
                    self.assertTrue(envelope(n, windows, block, budgets, Fraction(1), Fraction(2))[1])
                self.assertEqual(optimum, verify(n, windows, block, Fraction(1), Fraction(2),
                                                 result['budgets'], result['prices']))

    def test_two_slopes_at_integer_minimum_and_large_budgets(self):
        for n in range(5, 350, 2):
            if gcd(n, 6) == 1:
                self.assertEqual(two_slopes(n)['optimum'], solve(n, 1, 1)['optimum'])
        n = (2**491+1)*(2**509+1)
        if gcd(n,6) != 1:
            n += 2
        result = two_slopes(n)
        self.assertGreater(result['optimum'], 2**450)
        self.assertLessEqual(result['lower_peak'], n)

    def test_single_ratio_and_invalid_dual(self):
        n, r = 2537, Fraction(13, 10)
        result = solve(n, 3, 2, left=r, right=r)
        best = min(cover_cost(n, w, 2, r) for w in result['windows'])
        self.assertEqual(result['optimum'], best)
        with self.assertRaises(ValueError):
            verify(n, result['windows'], 2, r, r, result['budgets'], [(r, best+1)])
