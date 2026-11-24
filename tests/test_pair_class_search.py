from collections import defaultdict
from itertools import combinations
from math import gcd, isqrt, prod
import unittest
from unittest.mock import patch

from experiments.pair_class_search import check_source, search, sign_tables, square_class_key, square_product_root


class PairClassSearchTests(unittest.TestCase):
    def test_exact_root_of_small_signed_products(self):
        for first in range(-50, 51):
            for second in range(-50, 51):
                product = first * second
                expected = isqrt(product) if product > 0 else None
                if expected is not None and expected**2 != product:
                    expected = None
                self.assertEqual(square_product_root(first, second), expected, (first, second))

    def test_key_encodes_sign_odd_exponent_and_unit_character(self):
        primes = [p for p, _ in sign_tables()]
        for value in (1, -1, 2, -84, 3**39 * 5**8, -11 * 53**6):
            expected = int(value < 0)
            for p in primes:
                magnitude = abs(value)
                exponent = 0
                while magnitude % p == 0:
                    exponent += 1
                    magnitude //= p
                # Euler's criterion provides an independent reference for the table lookup.
                is_square = pow(magnitude, (p-1)//2, p) == 1
                expected = (expected << 2) + 2*(exponent % 2) + int(is_square)
            self.assertEqual(square_class_key(value), expected)
            self.assertNotEqual(square_class_key(value), square_class_key(-value))
            for multiplier in (*primes, 2, 59):
                self.assertEqual(square_class_key(value * multiplier**2), expected)
        with self.assertRaises(ValueError):
            square_class_key(0)

    def test_equal_keys_can_still_represent_different_square_classes(self):
        modulus = prod(p for p, _ in sign_tables())
        impostor = modulus**2 + 1
        self.assertEqual(square_class_key(1), square_class_key(impostor))
        self.assertIsNone(square_product_root(1, impostor))

        # Force all ten pairs of this known negative control to reach the exact test.
        work = search(437, 'unit', 0)
        with patch('experiments.pair_class_search.square_class_key', return_value=0):
            self.assertFalse(check_source(437, 282, work))
        self.assertEqual((work['possible_pairs'], work['exact_pair_tests']), (10, 10))
        self.assertIsNone(work['factor'])

    def test_every_unit_matches_direct_fraction_enumeration(self):
        n = 437
        fractions = defaultdict(list)
        for denominator in range(1, (n+1)//2):
            if gcd(denominator, n) != 1:
                continue
            inverse = pow(denominator, -1, n)
            for magnitude in range(1, (n-1)//(2*denominator)+1):
                if gcd(magnitude, denominator*n) != 1:
                    continue
                for numerator in (magnitude, -magnitude):
                    residue = numerator * inverse % n
                    fractions[residue].append((numerator, denominator))

        units = [x for x in range(1, n) if gcd(x, n) == 1]
        successful = set()
        for residue in units:
            expected = False
            for (a, b), (c, d) in combinations(fractions[residue], 2):
                product = a*b*c*d
                if product > 0 and isqrt(product)**2 == product:
                    expected = True
                    break
            work = search(n, 'unit', 0)
            self.assertEqual(check_source(n, residue, work), expected, residue)
            self.assertLessEqual(work['exact_pair_tests'], work['possible_pairs'])
            if expected:
                successful.add(residue)
                self.assertEqual(work['outcome'], 'pair')
                self.assertEqual(work['source_residue'], str(residue))
                (_, a, b), (_, c, d) = work['fractions']
                a, b, c, d = map(int, (a, b, c, d))
                self.assertIn((a, b), fractions[residue])
                self.assertIn((c, d), fractions[residue])
                self.assertNotEqual((a, b), (c, d))
                y = isqrt(a*b*c*d)
                self.assertEqual(y*y, a*b*c*d)
                self.assertEqual(work['factor'], gcd(residue*b*d-y, n))
                self.assertIn(work['factor'], (19, 23))
            else:
                self.assertEqual((work['factor'], work['outcome']), (None, 'no_split'))
        self.assertEqual(len(successful), 58)
        self.assertEqual(sum(x*x % n in successful for x in units), 64)

    def test_public_modes_and_immediate_divisors(self):
        self.assertNotIn(21, {x*x % 437 for x in range(437)})
        for mode, sample, residue, factor in (('unit', 21, 21, 19), ('square', 60, 104, 23)):
            with patch('experiments.pair_class_search.draw_root', return_value=(sample, 2)):
                work = search(437, mode, 1)
            self.assertEqual((work['source_residue'], work['factor']), (str(residue), factor))
            self.assertEqual((work['draws'], work['random_words']), (1, 2))
        with patch('experiments.pair_class_search.draw_root', return_value=(10, 1)):
            work = search(33, 'unit', 1)
        self.assertEqual((work['outcome'], work['factor']), ('coefficient_gcd', 3))
        with patch('experiments.pair_class_search.draw_root', return_value=(11, 1)):
            work = search(33, 'square', 1)
        self.assertEqual((work['outcome'], work['factor']), ('sample_gcd', 11))
