from math import gcd
import json
import unittest

from experiments.modular_curve_counts import (
    FIXTURE, check_fixture, coset_counts, dyadic_example, level_four, report, rounded_divisor_sum,
)


class ModularCurveCountTests(unittest.TestCase):
    def test_fixture_checks_completed_searches(self):
        measured = report()
        cases = json.loads(FIXTURE.read_text())
        check_fixture(measured, cases)
        cases[0]['factors'] = ['1', '527']
        with self.assertRaises(ValueError):
            check_fixture(measured, cases)
        self.assertEqual(measured['four_times_product']['factors'], [17, 31])

    def test_small_levels_against_primitive_pairs_and_congruence_roots(self):
        for level in range(2, 40):
            with self.subTest(level=level):
                result = coset_counts(level)
                units = [x for x in range(level) if gcd(x, level) == 1]
                # Units act freely on primitive columns, giving phi(level) columns per coset.
                primitive = sum(gcd(gcd(x, y), level) == 1
                                for x in range(level) for y in range(level))
                self.assertEqual(result['index'] * len(units), primitive)
                self.assertEqual(result['order_two_points'],
                                 sum((x*x+1) % level == 0 for x in range(level)))
                self.assertEqual(result['order_three_points'],
                                 sum((x*x+x+1) % level == 0 for x in range(level)))
                # Each divisor d contributes phi(gcd(d, level/d)) geometric cusps.
                expected_cusps = 0
                for d in range(1, level+1):
                    if level % d == 0:
                        common = gcd(d, level//d)
                        expected_cusps += sum(gcd(i, common) == 1 for i in range(common))
                self.assertEqual(result['cusps'], expected_cusps)
                self.assertEqual(sum(result['cusp_widths']), result['index'])
                self.assertEqual(result['work']['normalizations'], 2 * result['index'])
                self.assertEqual(result['work']['modular_inverses'], 2 * result['index'])
        self.assertEqual(coset_counts(37)['genus'], 2)

    def test_527_exact_genus_and_first_factor_seen(self):
        odd = coset_counts(527)
        self.assertEqual((odd['index'], odd['cusp_widths'], odd['genus']), (576, [1, 17, 31, 527], 47))
        self.assertEqual(odd['work']['unit_gcd_tests'], 1254)
        self.assertEqual(odd['first_normalization_factor']['unit_gcd_test'], 120)
        result = level_four(527)
        self.assertEqual((result['divisor_sum'], result['factor_sum'], result['factors']),
                         (576, 48, [17, 31]))
        counts = result['counts']
        self.assertEqual((counts['level'], counts['index'], counts['cusps'], counts['genus']),
                         (2108, 3456, 12, 283))
        self.assertEqual((counts['order_two_points'], counts['order_three_points']), (0, 0))
        self.assertEqual(counts['work']['unit_gcd_tests'], 10236)
        self.assertEqual(counts['first_normalization_factor'],
                         dict(divisor=17, normalization=80, unit_gcd_test=106))

    def test_dyadic_counts_and_strict_rounding_radius(self):
        n, p, q = 15, 3, 5
        d = (p+1)*(q+1)
        for a in (1, 2, 4):
            with self.subTest(a=a):
                result = dyadic_example(n, a)
                counts = result['counts']
                self.assertEqual(counts['index'], 12*a*a*d)
                self.assertEqual(counts['cusps'], 16*a)
                self.assertEqual((counts['order_two_points'], counts['order_three_points']), (0, 0))
                self.assertEqual(counts['genus'], a*a*d-8*a+1)
                self.assertEqual((result['divisor_sum'], result['factors']), (d, [p, q]))
                r = 2*a*a
                self.assertTrue(all(rounded_divisor_sum(counts['genus']+e, a) == d
                                    for e in range(-r+1, r)))
                self.assertEqual([row['divisor_sum'] for row in result['rounding']],
                                 [d-4, d, d, d, d, d+4, d+4])
        with self.assertRaises(ValueError):
            dyadic_example(n, 3)
        with self.assertRaises(ValueError):
            coset_counts(1)
