from collections import Counter
from fractions import Fraction
from itertools import product
from math import prod
import unittest

from experiments.cubic_trace_roots import characteristic, decode, readout, trace_roots


def field_product(left, right, d=11):
    out = [0, 0, 0]
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            wrap, k = divmod(i+j, 3)
            out[k] += x*y*(d**wrap)
    return out


class CubicTraceRootTests(unittest.TestCase):
    def test_true_and_false_polynomial_products(self):
        good = field_product(field_product([-2, 1, 0], [-2, 3, 0]), [4, 1, 0])
        bad = field_product(field_product([2, 1, 0], [-5, 2, 0]), [-10, 3, 0])
        self.assertEqual(good, field_product([7, -2, 0], [7, -2, 0]))
        self.assertEqual(characteristic(11, *good), (147, 10899, 255**2))
        self.assertEqual(characteristic(11, *bad), (498, 67488, 703**2))
        self.assertEqual(10**3 % 989, 11)
        self.assertEqual(prod((8, 28, 14)), 56**2)
        self.assertEqual(prod((12, 15, 20)), 60**2)
        yes = readout(989, 56, *characteristic(11, *good))
        self.assertEqual(yes['roots'], [21])
        self.assertEqual(yes['probes'], [{'trace': 21, 'modular_values': [46, 258], 'gcds': [23, 43]}])
        self.assertEqual(yes['proper_divisors'], [23, 43])
        entry, = yes['witnesses']
        r0, r1, r2 = map(lambda x: Fraction(x, entry['denominator']), entry['numerators'])
        root = [r0*(i == 0) + r1*x + r2*y for i, (x, y) in enumerate(zip(good, field_product(good, good)))]
        self.assertEqual(root, [7, -2, 0])
        no = readout(989, 60, *characteristic(11, *bad))
        self.assertEqual((no['roots'], no['proper_divisors'], no['status']), ([], [], 'no_trace'))
        self.assertEqual((no['work']['mod5_root_mask'], no['work']['integer_root_nodes']), (0, 0))
        with self.assertRaises(ValueError):
            readout(989, 57, *characteristic(11, *good))
        self.assertEqual(readout(989, 13, *characteristic(11, *good))['proper_divisors'], [])

    def test_scalar_and_repeated_roots(self):
        self.assertEqual(decode(0, 0, 0)['witnesses'][0]['numerators'], [0, 0, 0])
        self.assertEqual(decode(6, 12, 8)['status'], 'norm_not_square')
        self.assertEqual(decode(-3, 3, -1)['status'], 'norm_not_square')
        work = Counter()
        h = 2**256 + 37
        for sign in (1, -1):
            roots = trace_roots(3*h*h, 3*h**4, sign*h**3, work)
            self.assertEqual(roots, sorted((-sign*h, 3*sign*h)))
            self.assertLessEqual(work['integer_root_nodes'], work['max_isolation_nodes'])
            self.assertLessEqual(work['max_isolation_nodes'], 20*(h.bit_length()+5)+1)
        scalar = decode(12, 48, 64)
        self.assertEqual(scalar['roots'], [-2, 6])
        self.assertEqual(scalar['witnesses'], [dict(trace=6, second=12, numerators=[2, 0, 0], denominator=1)])
        self.assertEqual(trace_roots(14, 49, 6), [-4, -2, 0, 6])

    def test_signed_coefficients_and_complete_root_coverage(self):
        for a, b, w in product(range(-5, 6), range(-5, 6), range(-3, 4)):
            work = Counter()
            roots = trace_roots(a, b, w, work)
            expected = [x for x in range(-32, 33) if (x*x-a)**2 == 8*w*x+4*b]
            self.assertEqual(roots, expected, (a, b, w))
            self.assertLessEqual(work['radius'], 32)
            self.assertLessEqual(work['integer_root_nodes'], work['max_isolation_nodes'])


if __name__ == '__main__':
    unittest.main()
