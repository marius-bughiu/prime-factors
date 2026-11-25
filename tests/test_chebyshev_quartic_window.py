from fractions import Fraction
from itertools import combinations_with_replacement
import json
from math import isqrt
import unittest

from experiments.centered_sum_quartic import windows
from experiments.chebyshev_quartic_window import (
    envelope, evaluate, positive_on, probe, small_panel, volume_exponent,
)
from experiments.norm_auxiliary import multiply
from experiments.unit_quartic_probe import ROOT, local_values


class ChebyshevWindowTests(unittest.TestCase):
    def test_sturm_positivity_keeps_strict_endpoints_and_interior_contacts(self):
        roots = [Fraction(-2), Fraction(-1, 2), Fraction(0), Fraction(2, 3), Fraction(2)]
        for degree in range(5):
            for chosen in combinations_with_replacement(roots, degree):
                polynomial = [1]
                for root in chosen:
                    polynomial = multiply(polynomial, [-root.numerator, root.denominator])
                for sign in (1, -1):
                    p = [sign*v for v in polynomial]
                    for lo, hi in ((-3, 3), (-1, 1), (-2, 0), (0, 0), (1, 3)):
                        expected = evaluate(p, lo) > 0 and not any(lo <= r <= hi for r in chosen)
                        self.assertEqual(positive_on(p, lo, hi), expected, (p, lo, hi))
        self.assertTrue(positive_on([5, 0, -4, 0, 1], -4, 4))  # (x²−2)²+1
        self.assertFalse(positive_on([4, 0, -4, 0, 1], -4, 4))  # irrational double roots
        self.assertFalse(positive_on([], 1, 2))

    def test_every_certified_small_lane_agrees_with_division(self):
        curve_only = 0
        for n, exponent in ((143, 3), (437, 3), (10403, 3), (96577, 3),
                            (2102209, 4), (33525721, 4), (33525721, 5)):
            lo, hi, *_ = windows(n)
            r = 1 << exponent
            for u in range(1, r, 2):
                result = probe(n, exponent, u)
                self.assertIsNotNone(result['selected_row'], (n, r, u))
                expected = [[str(p), str(n//p)] for p in range(lo, isqrt(n)+1)
                            if n%p == 0 and n//p <= hi and u in (p%r, (n//p)%r)]
                self.assertEqual(result['pairs'], expected)
                curve_only += not any(row['l1_pass'] for row in result['rows'])
                self.assertEqual(int(result['unchecked_groups']), int(result['total_groups'])-1)
        self.assertEqual(curve_only, 2)

    def test_failed_rows_leave_a_true_factor_lane_unresolved(self):
        n = 33525721
        self.assertEqual(n, 4099*8179)
        self.assertEqual(4099%8, 3)
        result = probe(n, 3, 3)
        self.assertEqual(result['status'], 'no certified equation')
        self.assertIsNone(result['selected_row'])
        self.assertEqual(result['unchecked_groups'], result['total_groups'])
        self.assertEqual(result['remaining_cofactor'], str(n))

    def test_small_panel(self):
        self.assertEqual(small_panel(), dict(products=81, groups=366, occupied=81,
                                             l1_certified=210, l1_occupied_certified=42,
                                             curve_certified=253, curve_occupied_certified=47))

    def test_full_size_receipts(self):
        cases = json.loads((ROOT/'research/chebyshev-quartic-window.json').read_text())
        self.assertEqual([(v['source'], v['result']['exponent'], v['result']['status']) for v in cases],
                         [('unit-lane-crossed-2048', 611, 'factor pair found'),
                          ('unit-lane-crossed-2048', 610, 'no certified equation'),
                          ('unit-lane-fresh-2048', 610, 'certified empty lane'),
                          ('unit-lane-fresh-2048', 609, 'no certified equation')])
        for case in cases:
            n, result = int(case['n']), case['result']
            lo, hi, *_ = windows(n)
            self.assertEqual(case['volume_exponent'], volume_exponent(n, hi))
            self.assertEqual(len(case['lean_certificates']), len(result['pairs']))
            if result['selected_row'] is None:
                self.assertEqual(result['unchecked_groups'], result['total_groups'])
                continue
            radix = 1 << result['exponent']
            full = [c*n**max(0, 2-j) for j,c in enumerate(map(int, result['trace_coefficients']))]
            self.assertEqual(local_values(full, 1, radix), result['local_remainders'])
            self.assertFalse(any(any(v) for v in result['local_remainders'].values()))
            lower, upper = result['curve_permille']
            self.assertEqual(upper-lower, 1)
            m = 360*radix**4
            self.assertFalse(envelope(full, lower*m, lo, hi, scale=1000))
            self.assertTrue(envelope(full, upper*m, lo, hi, scale=1000))
            for p, q in result['pairs']:
                self.assertEqual(int(p)*int(q), n)
