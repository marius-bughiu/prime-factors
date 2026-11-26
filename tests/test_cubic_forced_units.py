import unittest
from collections import Counter
from math import gcd

from experiments.cubic_forced_units import (
    diagonal, divisors, exact_menu_support, irreducible, maximum_w, positions,
    readouts, representatives, sign_gcds, universal, varied,
)


class ForcedUnitTests(unittest.TestCase):
    def test_universal_square_set_and_gcd_source(self):
        found = set()
        for h in (1, -1):
            work = Counter()
            found.update(4*w-h for _, w in positions(1, 4, h, work))
            self.assertEqual(work['signed_divisor_tests'], 6)
        self.assertEqual(found, {9, 11, 27, 91})
        for n in range(3, 110, 2):
            result = universal(n)
            self.assertEqual(bool(result['ordinary_traces']), n in found)
            self.assertEqual(bool(result['projected_traces']), n in found)
        hit = universal(91)
        self.assertEqual(hit['elementary_gcds'], [[91, 1]])
        self.assertEqual(hit['ordinary_gcds'], [[91, 1]])
        self.assertEqual(hit['derivative_gcd'], 7)
        self.assertEqual(hit['projected_gcds'], [[91, 7]])

    def test_divisor_cut_and_irreducibility_against_integer_ranges(self):
        for r, t, h in ((1, 4, -1), (1, 9, 8), (4, 9, 5), (1, 16, 3)):
            reported = set(positions(r, t, h, Counter()))
            self.assertTrue(all(w <= maximum_w(r, t, h) for _, w in reported))
            for w in range(1, 33):
                # Any monic integer root has k+r dividing h.
                brute = all((k+r)*(k+t)*(k+w) != h for k in range(-r-abs(h), -r+abs(h)+1))
                self.assertEqual(irreducible(r, t, h, w, Counter()), brute)
                for u in range(-40, 41):
                    q = u**4-2*h*(2*w-r-t)*u*u-8*h*h*u+h*h*(r-t)**2
                    self.assertEqual((u, w) in reported, q == 0)
        for a in range(1, 40):
            self.assertEqual(divisors(a, Counter(), squared=True), [u for u in range(1,a*a+1) if a*a % u == 0])
        self.assertEqual(representatives(1, 4), {1: 1, 3: -1, 2: 2, 0: 4})

    def test_varied_semiprime_and_height_rejection(self):
        n = 1883747
        hit, = varied(n)['trace_hits']
        self.assertEqual((hit['r'], hit['t'], hit['h'], hit['w'], hit['u']), (1, 196, 9, 9611, -3))
        expected = [1193, 1579]
        self.assertEqual(hit['gcds'], expected)
        self.assertEqual(hit['readouts']['direct_gcds'], [expected])
        self.assertEqual(hit['readouts']['projected_gcds'], [expected])
        self.assertEqual(universal(n)['derivative_gcd'], 1)
        self.assertFalse(universal(n)['ordinary_traces'])
        self.assertEqual(hit['readouts']['derivative_gcd'], 1)
        self.assertEqual(gcd(n, 2*14*9*3), 1)
        with self.assertRaises(ArithmeticError):
            sign_gcds(n, 1, 196, 9, -4)
        with self.assertRaises(ValueError):
            readouts(n, 1, 196, 9, 9612)
        large = varied(2**2047 + 1)
        self.assertEqual(large['work']['height_exclusions'] + large['work']['no_representative'], 12)
        self.assertEqual(large['work'].get('signed_divisor_tests', 0), 0)
        self.assertEqual(exact_menu_support()['maximum_square_input'], 4198095)

    def test_public_diagonal_decode_and_neighbors(self):
        for s in (2, 3, 13, 2**340+1):
            n = 16*s**6-4*s*s-1
            split = diagonal(n)
            self.assertEqual(list(map(int, split['factors'])), [4*s**3-4*s*s+2*s-1, 4*s**3+4*s*s+2*s+1])
            self.assertEqual(int(split['fermat_tests_to_displayed_pair']), 2*s+1)
            for neighbor in (n-1, n+1, n+2):
                self.assertFalse(diagonal(neighbor)['factors'])
        self.assertFalse(diagonal(11)['factors'])
