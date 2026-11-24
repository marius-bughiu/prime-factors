from itertools import combinations
from math import gcd, isqrt, prod
import unittest

from experiments.universal_norm_batch import search, separating_search


def grid_gcds(n, side, coefficients=(1, 2, -2)):
    return {gcd(n, u*u+d*v*v) for d in coefficients
            for u in range(1, side+1) for v in range(1, side+1)}


class UniversalNormBatchTests(unittest.TestCase):
    def test_product_only_search_matches_each_small_grid(self):
        for p, q in combinations((11, 13, 17, 19, 23, 29, 31, 37), 2):
            n = p*q
            for side in (1, 2, 3, 4, 5, 7):
                width = min(side, isqrt(isqrt(n)))
                factors = grid_gcds(n, width) - {1, n}
                run = search(n, side)
                with self.subTest(n=n, side=side):
                    self.assertEqual(run['factor'] is not None, bool(factors))
                    if factors:
                        self.assertIn(run['factor'], factors)
                        delta, u, v, value = map(int, run['witness'])
                        self.assertTrue(1 <= u <= width and 1 <= v <= width)
                        self.assertEqual(u*u-delta*v*v, value)
                        self.assertEqual(gcd(value, n), run['factor'])

    def test_indefinite_batch_needing_disaggregation(self):
        n = 713
        self.assertEqual(grid_gcds(n, 4, (1, 2)), {1})
        self.assertEqual(grid_gcds(n, 3), {1})
        entire = prod(u*u-2*v*v for u in range(1, 5) for v in range(1, 5))
        self.assertEqual(gcd(n, entire), n)
        self.assertIsNone(search(n, 3)['factor'])
        run = search(n, 4)
        self.assertIn(run['factor'], (23, 31))
        self.assertEqual(run['whole_modulus_batches'], 1)
        self.assertEqual(run['witness'][0], 2)
        self.assertGreater(run['leaf_gcds'], 0)

    def test_target_grid_covers_distinct_primes_including_unbalanced_products(self):
        primes = (3, 5, 7, 11, 13, 23, 31, 37, 59, 61, 97)
        for p, q in combinations(primes, 2):
            run = search(p*q, 100)
            self.assertIn(run['factor'], (p, q), (p, q))
            if q <= 2*p:
                promised = search(p*q, 100, balanced=True)
                self.assertIn(promised['factor'], (p, q), (p, q))
                if len(promised['discriminants']) == 1:
                    delta = promised['discriminants'][0]
                    self.assertNotEqual(pow(delta, (p-1)//2, p) == 1,
                                        pow(delta, (q-1)//2, q) == 1)
                    self.assertEqual(promised['whole_modulus_batches'], 0)

    def test_balanced_grid_can_choose_the_larger_prime(self):
        n = 1900014700027
        ordinary = search(n, 1024)
        self.assertEqual((ordinary['factor'], ordinary['witness']),
                         (1000003, [-2, '151', '699', '1000003']))
        self.assertIsNone(search(n, 1024, balanced=True)['factor'])
        promised = search(n, 2048, balanced=True)
        self.assertEqual((promised['discriminants'], promised['factor']), ([-1], 1900009))
        self.assertEqual(int(promised['side']), isqrt(isqrt(2*n)))

    def test_empty_grids_and_invalid_inputs(self):
        # All signed norms in this public box are below a promised factor.
        n = 594976573900310730017789
        r = search(n, 512, balanced=True)
        self.assertEqual(r['outcome'], 'below_factor_range')
        self.assertEqual((r['degree'], r['evaluations'], r['batch_gcds']), (0, 0, 0))
        self.assertEqual(r['empty_forms'], len(r['discriminants']))
        self.assertIsNone(r['factor'])
        capped = search(n, 0)
        self.assertEqual((capped['outcome'], capped['factor'], capped['degree']),
                         ('side_limit', None, 0))
        self.assertIsNone(search(3, 1)['factor'])
        for n, cap in ((1, 2), (10, 2), (21, -1)):
            with self.assertRaises(ValueError):
                search(n, cap)

    def test_single_coefficient_selects_exactly_one_local_square(self):
        primes = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)
        for p, q in combinations(primes, 2):
            if q > 2*p:
                continue
            n = p*q
            for cap in (2, 10):
                r = separating_search(n, cap, 100)
                b = r['selector']
                if r['outcome'] == 'selector_gcd':
                    self.assertEqual(r['factor'], gcd(b, n))
                    self.assertEqual(r['batch_gcds'], 0)
                    continue
                self.assertIsNotNone(b)
                square_at = [prime for prime in (p, q) if pow(b, (prime-1)//2, prime) == 1]
                self.assertEqual(len(square_at), 1)
                width = int(r['side'])
                expected = grid_gcds(n, width, (-b,))-{1}
                with self.subTest(n=n, cap=cap):
                    self.assertEqual(r['factor'] is not None, bool(expected))
                    if expected:
                        self.assertEqual(expected, set(square_at))
                        self.assertEqual(r['factor'], square_at[0])
                    if width == int(r['target_side']):
                        self.assertIsNotNone(r['factor'])
                    self.assertEqual((r['evaluations'], r['pair_values_covered'], r['batch_gcds']),
                                     (width, width*width, 1))

    def test_selector_and_grid_budgets_are_distinct(self):
        r = separating_search(713, 6, 2)
        self.assertEqual((r['outcome'], r['selector_tests'], r['evaluations']),
                         ('selector_limit', 1, 0))
        r = separating_search(713, 0, 739)
        self.assertEqual((r['outcome'], r['selector'], r['batch_gcds']), ('side_limit', 3, 0))
        r = separating_search(713, 6, 739)
        self.assertEqual((r['outcome'], r['factor'], r['batch_gcds']), ('separating_gcd', 23, 1))
        r = separating_search(15, 0, 739)
        self.assertEqual((r['outcome'], r['factor'], r['batch_gcds']), ('selector_gcd', 3, 0))
        for args in ((2, 10, 10), (15, -1, 10), (15, 10, 0)):
            with self.assertRaises(ValueError):
                separating_search(*args)
