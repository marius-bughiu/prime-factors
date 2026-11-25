import unittest
from math import gcd, prod

from experiments.binomial_divisor_window import SIFTED_DENOMINATORS, SIFTED_NODES, jet_rows, search, sifted_basis
from experiments.higher_divisor_window import check_row
from experiments.quartic_divisor_window import evaluate


class SiftedDivisorWindowTests(unittest.TestCase):
    def test_basis_integrality_and_weight_on_every_eligible_point(self):
        for shift in range(-52, 53):
            radius = 30
            rows, weights = sifted_basis(shift, radius)
            for i, (row, weight, denominator) in enumerate(zip(rows, weights, SIFTED_DENOMINATORS)):
                for x in range(-radius, radius + 1):
                    if gcd(x + shift, 105) != 1:
                        continue
                    value, remainder = divmod(prod(x + shift - a for a in SIFTED_NODES[:i]), denominator)
                    self.assertEqual(remainder, 0)
                    self.assertLessEqual(abs(value), weight)
                    self.assertEqual(evaluate(row, x), 45360 * value)

    def test_anchor_basis_and_both_centered_searches(self):
        n, first, span = 132079, 253, 32
        options = dict(centered=True, degree=6, depth=3)
        new = search(n, first, span, sifted=True, **options)
        old = search(n, first, span, **options)
        self.assertEqual((new['origin'], new['shift'], new['denominator']), (285, -15, 45360))
        self.assertEqual((2*new['shift'] - new['origin']) % 105, 0)
        self.assertTrue(new['short'])
        self.assertFalse(old['short'])
        self.assertEqual(new['divisors'], [d for d in range(first, first + 2*span + 1, 2) if n % d == 0])
        basis, _ = sifted_basis(new['shift'], span // 2)
        for v in jet_rows(n, new['anchor'], 6, 3, basis):
            ordinary = [sum(a * row[j] for a, row in zip(v, basis)) for j in range(7)]
            check_row(n, new['anchor'], span, 3, ordinary)

    def test_public_gcd_precedes_lattice_and_catches_seven(self):
        for n, expected in ((7*23, 7), (35, 5), (7, None)):
            w = search(n, 11, 12, centered=True, sifted=True, degree=6, depth=3)
            self.assertEqual(w['denominator_factor'], expected)
            self.assertFalse(w['excluded'])
            self.assertFalse(w['work'])
        for degree, centered in ((4, True), (6, False)):
            with self.assertRaises(ValueError):
                search(143, 9, 16, centered=centered, sifted=True, degree=degree, depth=2)
