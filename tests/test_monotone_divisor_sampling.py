import unittest
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt

from experiments.monotone_divisor_sampling import scan


class MonotoneDivisorSamplingTest(unittest.TestCase):
    def test_predicted_maximum_on_two_periods(self):
        primes = [x for x in range(2, 62)
                  if all(x % d for d in range(2, isqrt(x) + 1))]
        for p, q in combinations(primes, 2):
            with self.subTest(p=p, q=q):
                n = p * q
                left, right = pow(p, -1, q), pow(q, -1, p)
                k = max(left, right)
                predicted = Fraction((p + q) * k - 1, n * k)
                measured = scan(n, 2 * n)
                self.assertEqual(Fraction(measured['best_hits'], measured['best_end']),
                                 predicted)
                endpoint = p * left if left >= right else q * right
                count = sum(1 < gcd(n, x) < n for x in range(1, endpoint + 1))
                self.assertEqual(Fraction(count, endpoint), predicted)
                self.assertEqual(measured['first_hit'], p)
                self.assertEqual(measured['factor'], gcd(n, measured['best_end']))

    def test_empty_or_exhausted_prefix(self):
        for limit in (0, 1, 6):
            measured = scan(77, limit)
            self.assertEqual(measured['gcd_tests'], limit)
            self.assertIsNone(measured['factor'])
            self.assertIsNone(measured['best_end'])
