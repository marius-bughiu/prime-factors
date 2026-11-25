from itertools import product
from math import gcd, isqrt
import unittest

from experiments.class_order_search import Forms, search, window_events


def reduced_forms(D):
    return {(a, b, c)
            for a in range(1, isqrt((-D)//3)+1)
            for b in range(-a+1, a+1)
            for c, rem in [divmod(b*b-D, 4*a)]
            if rem == 0 and a <= c and (a != c or b >= 0) and gcd(a, gcd(b, c)) == 1}


class ClassOrderSearchTests(unittest.TestCase):
    def test_group_arithmetic_on_all_reduced_classes(self):
        for D, h in [(-23, 3), (-39, 4), (-55, 4), (-84, 4), (-120, 4), (-231, 12)]:
            group = Forms(D, 100000)
            classes = reduced_forms(D)
            self.assertEqual(len(classes), h)
            table = {(x, y): group.multiply(x, y) for x, y in product(classes, repeat=2)}
            self.assertEqual(set(table.values()), classes)
            for x in classes:
                self.assertEqual(table[x, group.identity], x)
                self.assertEqual(table[x, group.inverse(x)], group.identity)
                self.assertEqual(group.power(x, h), group.identity)
            for x, y, z in product(classes, repeat=3):
                self.assertEqual(table[table[x,y],z], table[x,table[y,z]])
                self.assertEqual(table[x,y], table[y,x])

    def test_consecutive_hits_and_overhang(self):
        group = Forms(-23, 100000)
        x = group.seed(2)
        for low in range(1, 16):
            for high in range(low, low+18):
                result = list(window_events(group, x, low, high, {'giant_lookups': 0}))
                if isqrt(high-low)+1 >= 3:
                    self.assertEqual(result, [('order', 3)])
                else:
                    self.assertEqual(result, [('hit', k) for k in range(low, high+1) if k%3 == 0])

    def test_shared_window_and_single_pivot(self):
        for n, prime, cases in [
            (24511, 7, (46, 72)),
            (7237264777, 43, (1702, 10374)),
        ]:
            for shared, expected in zip([True, False], cases):
                result = search(n, prime, 12000, shared)
                self.assertEqual(result['compositions'], expected)
                self.assertIn(result['factor'], [127, 193] if n == 24511 else [71593, 101089])
            if n != 24511:
                self.assertEqual(result['outcome'], 'combined involutions')

    def test_budgets_and_no_usable_seed(self):
        for n, limit, budget, outcome in [(24511, 7, 0, 'composition limit'),
                                           (24511, 1, 100, 'seed limit'),
                                           (24511, 7, 45, 'composition limit')]:
            result = search(n, limit, budget)
            self.assertEqual(result['outcome'], outcome)
            self.assertIsNone(result['factor'])
            self.assertLessEqual(result['compositions'], budget)
        self.assertEqual(search(143, 13, 0)['factor'], 11)
