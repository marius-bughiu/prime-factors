import unittest
from collections import Counter
from math import isqrt

from experiments.reduced_weight_discriminant import discriminant_root


class ReducedWeightDiscriminantTest(unittest.TestCase):
    def test_returns_full_roots_for_all_signs(self):
        for radix in (1, 2, 6, 420):
            work = Counter()
            for reduced in range(-1, 1000):
                full = reduced * radix**2
                expected = None
                if full >= 0 and isqrt(full)**2 == full:
                    expected = isqrt(full)
                self.assertEqual(discriminant_root(full, radix, work), expected)
            self.assertEqual(work['nonnegative_discriminants'], 1000)
            self.assertLess(work['square_tests'], work['nonnegative_discriminants'])

    def test_invalid_stationary_trace(self):
        for value in (-41, 41):
            with self.assertRaises(ArithmeticError):
                discriminant_root(value, 2, Counter())
