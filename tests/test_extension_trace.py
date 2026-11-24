from collections import Counter
from itertools import product
from math import gcd
import unittest

from experiments.extension_trace import punctured_search, search


def prime_field_counts(p, a, b):
    """At each x, count affine y on the cubic, minus the baseline one."""
    roots = Counter(y*y % p for y in range(p))
    return [roots[(x**3+a*x+b) % p]-1 for x in range(p)]


def extension_field_counts(p, d, a, b, *, punctured=False):
    """Literal point counts in F_p[T]/(T²-d), using pair multiplication."""
    def mul(z, w):
        x, y = z
        u, v = w
        return ((x*u+d*y*v) % p, (x*v+y*u) % p)

    elements = list(product(range(p), repeat=2))
    roots = Counter(mul(z, z) for z in elements)
    counts = []
    for z in elements:
        u, v = mul(mul(z, z), z)
        f = ((u+a*z[0]+b) % p, (v+a*z[1]) % p)
        if punctured:
            shift = (z[0]-2, z[1])
            f = mul(mul(shift, shift), f)
        counts.append(roots[f]-1)
    return counts


class ExtensionTraceTests(unittest.TestCase):
    def test_complete_sums_match_literal_product_of_fields(self):
        for p, q, a, b in [(3, 7, 1, 1), (5, 7, 1, 1), (7, 11, 1, 1),
                           (7, 11, 0, 1), (7, 11, -1, 0), (5, 13, 1, 1)]:
            n = p*q
            with self.subTest(n=n, a=a, b=b):
                result = search(n, n*n, 8, a, b)
                d = result['selector']
                r, s = (q, p) if d % p in {x*x % p for x in range(p)} else (p, q)
                base_r = prime_field_counts(r, a, b)
                base_s = prime_field_counts(s, a, b)
                field_r = extension_field_counts(r, d, a, b)
                self.assertEqual(sum(field_r), 2*r-sum(base_r)**2)
                # The quadratic algebra over N is F_(r²) × F_s × F_s.
                expected = sum(x*y*z for x, y, z in product(field_r, base_s, base_s))
                self.assertEqual(result['extension_sum'], str(expected))
                base = sum(x*y for x, y in product(base_r, base_s))
                self.assertEqual(result['base_sum'], str(base))
                self.assertEqual(base*base+expected, 2*r*sum(base_s)**2)
                divisor = r if gcd(s, sum(base_s)) == 1 else n
                self.assertEqual(result['trace_gcd'], str(divisor))
                self.assertEqual(result['factor'], r if divisor == r else None)
                self.assertEqual(result['base_symbol_evaluations'], n)
                self.assertEqual(result['extension_symbol_evaluations'], n*n-n)

    def test_partial_grid_never_reaches_readout(self):
        for budget in [0, 1, 76, 77, 78, 77**2-1]:
            result = search(77, budget, 2)
            self.assertEqual(result['outcome'], 'position_limit')
            self.assertEqual(result['positions'], budget)
            self.assertEqual(result['base_symbol_evaluations'], (budget+76)//77)
            self.assertEqual(result['extension_symbol_evaluations'], budget-(budget+76)//77)
            for key in ['factor', 'base_sum', 'extension_sum', 'trace_gcd']:
                self.assertIsNone(result[key])

    def test_setup_divisors_and_limits(self):
        for n, limit, a, b, outcome, factor in [
                (341, 8, 1, 1, 'discriminant_divisor', 31),
                (77, 8, 0, 0, 'singular_curve', None),
                (15, 4, 1, 1, 'selector_divisor', 3),
                (65, 2, 1, 1, 'selector_limit', None)]:
            result = search(n, 10, limit, a, b)
            self.assertEqual((result['outcome'], result['factor']), (outcome, factor))
            self.assertEqual(result['positions'], 0)
        with self.assertRaises(ValueError):
            search(12, 4, 3)

    def test_punctured_point_counts_and_verified_reconstruction(self):
        for p, q in [(7, 11), (7, 13), (5, 13), (5, 17), (13, 17)]:
            n = p*q
            with self.subTest(n=n):
                result = punctured_search(n, n*n, 8)
                d = result['selector']
                r, s = (q, p) if d % p in {x*x % p for x in range(p)} else (p, q)
                base_r, base_s = prime_field_counts(r, -1, 0), prime_field_counts(s, -1, 0)
                # At x=2 the cubic equals 6. Its centered point count is χ(6).
                u, v = base_s[2]*sum(base_s), base_r[2]*sum(base_r)
                self.assertEqual(result['local_traces'], [str(t) for t in sorted([u,v])])
                self.assertEqual(result['normalized_base_sum'], str(u*v))
                self.assertEqual(result['normalized_marked_sum'], str((u-1)*(v-1)))
                field_r = extension_field_counts(r, d, -1, 0, punctured=True)
                marked_s = base_s[:]
                marked_s[2] = 0
                expected = sum(x*y*z for x, y, z in product(field_r, marked_s, marked_s))
                self.assertEqual(result['extension_sum'], str(expected))
                self.assertEqual(expected, (u-1)**2 * (2*r-v*v-1))
                self.assertEqual(result['factor'], r)
                self.assertEqual(result['base_symbol_evaluations'], 2*n)
                self.assertEqual(result['extension_symbol_evaluations'], n*n-n)
        self.assertEqual(punctured_search(65, 65**2, 3)['assignments_tested'], 2)

    def test_punctured_setup_and_caps(self):
        for budget in [0, 1, 77, 78, 77**2-1]:
            result = punctured_search(77, budget, 2)
            self.assertEqual(result['outcome'], 'position_limit')
            self.assertEqual(result['positions'], budget)
            self.assertEqual(result['base_symbol_evaluations'], 2*((budget+76)//77))
            self.assertEqual(result['assignments_tested'], 0)
            for key in ['factor', 'normalized_base_sum', 'normalized_marked_sum',
                        'extension_sum', 'local_traces']:
                self.assertIsNone(result[key])
        self.assertEqual(punctured_search(21, 0, 2)['factor'], 3)
        self.assertEqual(punctured_search(3, 0, 2)['outcome'], 'invalid_mark')
        self.assertEqual(punctured_search(65, 0, 2)['outcome'], 'selector_limit')
