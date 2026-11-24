from collections import Counter
from math import gcd, isqrt, prod
from random import Random
import unittest

from experiments.factorial_progressions import (
    block_products, decimal_convolution, extend_right, factorial_tables, search,
)
from experiments.wide_modulus import multiply


class FactorialProgressionTests(unittest.TestCase):
    def test_exact_packing_including_zero_limbs_and_maximum_coefficients(self):
        rng = Random(58073)
        for n in (81, 1009*1013, 2**2048-159):
            trials = [([0], [0]), ([n-1]*17, [n-1]*21)]
            for _ in range(10):
                trials.append(([rng.randrange(n) for _ in range(6)],
                               [rng.randrange(n) for _ in range(11)]))
            for a, b in trials:
                expected = [sum(x*b[h-i] for i, x in enumerate(a) if 0 <= h-i < len(b)) % n
                            for h in range(len(a)+len(b)-1)]
                self.assertEqual(decimal_convolution(a, b, n), expected)

    def test_integer_index_interpolation_matches_literal_polynomial_values(self):
        n = 101*103
        rng = Random(321)
        f, inv, found = factorial_tables(70, n, Counter())
        self.assertIsNone(found)
        for size in range(1, 19):
            coeffs = [rng.randrange(n) for _ in range(size)]
            values = [sum(c*t**i for i, c in enumerate(coeffs)) % n for t in range(71)]
            for last in (0, size-1, size, 3*size+1, 70):
                for convolution in (multiply, decimal_convolution):
                    self.assertEqual(extend_right(values[:size], last, f, inv, n, convolution,
                                                  Counter()), values[:last+1])

    def test_each_computed_block_equals_its_direct_wheel_product(self):
        n = 1009*1013
        for wheel in (2, 6, 30):
            residues = [r for r in range(1, wheel) if gcd(r, wheel) == 1]
            for cycles in (1, 2, 7, 18, 127, 192):
                base = 73*wheel
                blocks, size, found = block_products(base, cycles, wheel, residues, n, multiply,
                                                      Counter())
                self.assertIsNone(found)
                expected = [prod(base+j*wheel+r for j in range(i*size, (i+1)*size)
                                 for r in residues) % n for i in range(cycles//size)]
                self.assertEqual(blocks, expected)

    def test_alignment_caps_and_products_against_direct_scan(self):
        for n in (89, 101*173, 313*367, 1009*1033, 4093*4513):
            for wheel in (2, 3, 6, 30, 210):
                lo, hi = isqrt((n-1)//2)+1, isqrt(n)
                for cap in (0, 1, 3, 29, 72, 97, hi-lo+1, None):
                    r = search(n, cap, wheel=wheel)
                    if r['outcome'] in ('interpolation_divisor', 'wheel_divisor'):
                        self.assertTrue(1 < r['factor'] < n and n % r['factor'] == 0)
                        self.assertFalse(r['interval_complete'])
                        continue
                    end = hi if cap is None else min(hi, lo+cap-1)
                    direct = [a for a in range(lo,end+1) if gcd(a, wheel) == 1]
                    expected = prod(direct) % n
                    w = r['work']
                    self.assertEqual(int(r['product']), expected)
                    self.assertEqual(w.get('edge_candidates', 0)+w.get('batched_candidates', 0),
                                     len(direct))
                    self.assertEqual(r['interval_complete'], end == hi)
                    self.assertEqual(r['factor'], gcd(expected, n) if gcd(expected,n)>1 else None)

    def test_nonunit_factorial_setup_and_small_wheel_divisors(self):
        for n, last in ((101*103, 101), (101*103, 104)):
            _, _, p = factorial_tables(last, n, Counter())
            self.assertIn(p, (101, 103))
        self.assertEqual(search(15, 10, wheel=30)['factor'], 3)
        self.assertIsNone(search(5, 10, wheel=30)['factor'])
        for n, cap, w in ((20, 2, 30), (15, -1, 2), (15, 2, 1)):
            with self.assertRaises(ValueError):
                search(n, cap, wheel=w)
