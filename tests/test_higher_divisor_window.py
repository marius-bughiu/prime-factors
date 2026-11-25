import unittest

from experiments.higher_divisor_window import basis, check_row, search


class HigherDivisorWindowTests(unittest.TestCase):
    def test_centered_basis_reproduces_required_jets(self):
        # Use negative and positive anchors, including an odd input divisible by 3.
        for n, anchor, depth, degree in [(15, -7, 3, 4), (91, 17, 4, 8)]:
            for i, row in enumerate(basis(n, anchor, degree, depth)):
                self.assertEqual(row[i], n**max(depth-i, 0))
                self.assertGreater(check_row(n, anchor, 2, depth, row), 0)
        with self.assertRaises(ArithmeticError):
            check_row(15, -7, 2, 3, [49, 14, 1])
        with self.assertRaises(ValueError):
            check_row(15, -7, 2, 3, [0, 0, 0, 0])

    def test_unsuccessful_length_bound_cannot_exclude(self):
        report = search(91, 11, 4, degree=2, depth=2, modulus_limit=7)
        self.assertFalse(report['short'])
        self.assertFalse(report['excluded'])
        self.assertIsNone(report['rootless_modulus'])

    def test_divisors_below_and_above_the_center(self):
        for n in (143, 169, 437, 2501):
            for center in (11, 21, 43):
                report = search(n, center, 2, degree=6, depth=3, modulus_limit=17)
                if report['short']:
                    direct = [d for d in range(center-4, center+5, 2) if n % d == 0]
                    self.assertEqual(report['divisors'], direct)
                    self.assertEqual(report['excluded'], not direct)
