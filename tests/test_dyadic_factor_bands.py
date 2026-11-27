import unittest
from itertools import combinations
from math import comb, gcd, isqrt

from experiments.dyadic_factor_bands import cut, search


class DyadicFactorBandTests(unittest.TestCase):
    def test_masks_agree_at_every_examined_level(self):
        for bits in range(3, 8):
            primes = [p for p in range((1 << (bits - 1)) + 1, 1 << bits, 2)
                      if all(p % d for d in range(3, isqrt(p) + 1, 2))]
            for p, q in combinations(primes, 2):
                n = p * q
                result = search(n, isqrt(n), wheel=1)
                self.assertEqual(result['factors'], [str(p), str(q)])
                self.assertEqual(result['rows'][-1]['index'], (p ^ q).bit_length() - 1)
                for row in result['rows']:
                    a = n >> row['index']
                    h = a // 2
                    expected = gcd(n, comb(2 * h, h) * (a if a % 2 else 1))
                    self.assertEqual(row['mask_gcd'], str(expected))

    def test_missing_part_of_a_band_cannot_be_declared_a_miss(self):
        result = search(3127, 2)
        self.assertEqual(result['rows'][0]['mask_gcd'], '3127')
        self.assertIsNone(result['rows'][1]['mask_gcd'])
        self.assertEqual(result['remaining'], ['3127'])

    def test_empty_public_box_spends_no_budget(self):
        result = search(63, 11, wheel=1)
        self.assertEqual(result['examined'], 0)
        self.assertEqual(result['rows'], [])
        self.assertEqual(result['remaining'], ['63'])

    def test_common_prefix_cutoff(self):
        for p in range(3, 52):
            for q in range(p + 1, 63):
                n = p * q
                for j in range(6):
                    self.assertEqual((p >> j) == (q >> j), cut(n, isqrt(n), j) <= p)
