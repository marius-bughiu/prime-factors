import unittest
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt

from experiments.monotone_divisor_sampling import scan, scan_sum_rectangles


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

    def test_two_draw_rectangles_match_direct_gcd_counts(self):
        for n in (2, 6, 15, 21, 35, 77):
            for limit in (0, 1, 3, 5, 8):
                with self.subTest(n=n, limit=limit):
                    side = min(n, limit)
                    result = scan_sum_rectangles(n, limit)
                    brute = {}
                    for a in range(1, side + 1):
                        for b in range(a, side + 1):
                            count = sum(1 < gcd(n, x+y) < n
                                        for x in range(1, a+1) for y in range(1, b+1))
                            brute[a, b] = Fraction(count, a*b)
                    self.assertEqual(result['rectangles_tested'], len(brute))
                    self.assertEqual(result['sum_gcd_tests'], max(0, 2*side-1))
                    self.assertEqual(result['cutoff_gcd_tests'], int(side > 0))
                    if brute:
                        a, b = max(brute, key=brute.get)
                        self.assertEqual((result['best_a'], result['best_b']), (a, b))
                        self.assertEqual(Fraction(result['best_hits'], a*b), brute[a, b])
                        self.assertEqual(result['cutoff_gcd'], gcd(n, b+1))
                    else:
                        self.assertIsNone(result['factor'])
                        self.assertIsNone(result['best_a'])
                        self.assertIsNone(result['cutoff_gcd'])

    def test_truncated_cutoff_retains_factor_already_seen(self):
        result = scan_sum_rectangles(77, 5)
        self.assertEqual(result['first_hit_sum'], 7)
        self.assertEqual(result['first_hit_gcd'], 7)
        self.assertEqual((result['best_a'], result['best_b']), (5, 5))
        self.assertEqual(result['cutoff_gcd'], 1)
        self.assertEqual(result['factor'], 7)
        self.assertEqual(result['factor_source'], 'sum_table')
