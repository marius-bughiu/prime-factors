from itertools import combinations
from math import gcd
import unittest

from experiments.gap_coverage import primes_through
from experiments.weighted_stride_search import geometric_values, root_polynomial, search


class WeightedStrideSearchTests(unittest.TestCase):
    def test_product_tree_and_chirp_over_composite_ring(self):
        n = 77
        for size in [0, 1, 12, 13, 127, 259]:
            roots = [(3*j*j+2*j+4) % n for j in range(size)]
            poly = root_polynomial(roots, n)
            self.assertEqual((len(poly), poly[-1]), (size+1, 1))
            for h, count in [(4, 1), (2, 35), (1, 5)]:
                expected = []
                for index in range(count):
                    point = pow(h, index, n)
                    value = 1
                    for root in roots:
                        value = value*(point-root) % n
                    expected.append(value)
                self.assertEqual(geometric_values(poly, h, count, n), expected)

    def test_complete_tables_on_balanced_products(self):
        for p, q in combinations(primes_through(79)[2:], 2):
            if q > 2*p:
                continue
            n = p*q
            for stride in (1, 24):
                r = search(n, 4, 3, 1000, stride=stride)
                if r['outcome'] == 'short_order':
                    h = pow(2, stride, n)
                    self.assertTrue(any(pow(h, i, n) == 1 for i in (1, 2)))
                    self.assertTrue(all(gcd(pow(h, i, n)-1, n) in (1,n) for i in (1,2)))
                else:
                    self.assertIn(r['factor'], (p, q))

    def test_order_and_collision_refinement(self):
        order = search(77, 8, 8, 200)
        self.assertEqual((order['outcome'], order['factor']), ('order_divisor', 7))
        self.assertGreater(order['work']['order_gcds'], 1)
        exact = search(35, 1, 1, 4)
        self.assertEqual((exact['outcome'], exact['factor']), ('trace_divisor', 5))
        split = search(35, 2, 4, 20, stride=1, beta=3)
        self.assertEqual(split['outcome'], 'collision_divisor')
        self.assertGreater(split['work']['collision_gcds'], 1)
        rejected = search(1900014700027, 3, 1, 30, beta=1)
        self.assertEqual(rejected['outcome'], 'giant_limit')
        self.assertEqual(rejected['work']['equality_checks'], 30)
        self.assertIsNone(rejected['factor'])

    def test_public_caps(self):
        for key, call in [
                ('baby_limit', lambda: search(1900014700027, 100, 10**50, 10)),
                ('giant_limit', lambda: search(1900014700027, 8, 20, 0)),
                ('slope_limit', lambda: search(1900014700027, 10**50, 1, 10, max_slopes=2))]:
            result = call()
            self.assertFalse(result['schedule_complete'])
            self.assertEqual((result['factor'], result['limit'], result['outcome']), (None,key,key))
        with self.assertRaises(ValueError):
            search(77, 3, 4, 20, stride=8)
