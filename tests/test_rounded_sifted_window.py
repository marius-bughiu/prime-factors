import unittest
from math import gcd

from experiments.binomial_divisor_window import SIFTED_DENOMINATORS, rounded_basis, search, sifted_basis
from experiments.quartic_divisor_window import evaluate


class RoundedSiftedWindowTests(unittest.TestCase):
    def test_signed_corrections_and_weights_on_eligible_integers(self):
        for radius in (4, 12, 30):
            u = radius // 2
            for shift in range(-52, 53):
                polynomials, weights, corrections = rounded_basis(shift, radius)
                old, _ = sifted_basis(shift, radius)
                for x in range(-radius, radius + 1):
                    if gcd(x + shift, 105) != 1:
                        continue
                    chebyshev = [2, x]
                    while len(chebyshev) < 7:
                        chebyshev.append(x * chebyshev[-1] - u**2 * chebyshev[-2])
                    chebyshev[0] = 1
                    for i, divisor in enumerate(SIFTED_DENOMINATORS):
                        errors = corrections[i]
                        self.assertEqual(len(errors), 7)
                        self.assertFalse(any(errors[i:]))
                        self.assertTrue(all(-divisor < 2 * a <= divisor for a in errors))
                        scale = 45360 // divisor
                        cleared = evaluate(polynomials[i], x)
                        self.assertEqual(cleared, scale * (chebyshev[i] + evaluate(errors, x)))
                        self.assertEqual((cleared - evaluate(old[i], x)) % 45360, 0)
                        quotient, remainder = divmod(cleared, 45360)
                        self.assertEqual(remainder, 0)
                        self.assertLessEqual(abs(quotient), weights[i])

    def test_small_factor_hit_and_matched_miss(self):
        options = dict(degree=6, depth=3, centered=True)
        rounded = search(132079, 237, 48, rounded=True, **options)
        previous = search(132079, 237, 48, sifted=True, **options)
        self.assertEqual((rounded['origin'], rounded['shift'], rounded['divisors']), (285, -15, [269]))
        self.assertTrue(rounded['short'])
        self.assertFalse(previous['short'])
        self.assertEqual(rounded['height'], 7523281)

    def test_precheck_and_supported_radii(self):
        w = search(161, 13, 12, centered=True, rounded=True, degree=6, depth=3)
        self.assertEqual(w['denominator_factor'], 7)
        self.assertFalse(w['corrections'])
        self.assertFalse(w['work'])
        with self.assertRaises(ValueError):
            search(143, 9, 10, centered=True, rounded=True, degree=6, depth=3)
        with self.assertRaises(ValueError):
            search(143, 9, 12, centered=True, rounded=True, degree=4, depth=2)
