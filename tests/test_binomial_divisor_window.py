import unittest
from math import comb, factorial

from experiments.binomial_divisor_window import cleared_basis, jet_rows, search
from experiments.higher_divisor_window import check_row
from experiments.quartic_divisor_window import evaluate


class BinomialDivisorWindowTests(unittest.TestCase):
    def test_integer_normalization_and_all_taylor_conditions(self):
        for degree in range(2, 8):
            basis = cleared_basis(degree)
            for i, row in enumerate(basis):
                for x in range(12):
                    self.assertEqual(evaluate(row, x), factorial(degree)*comb(x, i))
            for row in jet_rows(143, -17, degree, 2, basis):
                cleared = [sum(a*b[j] for a, b in zip(row, basis)) for j in range(degree+1)]
                check_row(143, -17, 12, 2, cleared)

    def test_every_returned_short_row_covers_its_inclusive_window(self):
        for n in (143, 221, 667, 2501):
            for first in (7, 11, 17, 33):
                result = search(n, first, 8, degree=4, depth=2)
                if result['short']:
                    self.assertEqual(result['divisors'], [d for d in range(first,first+17,2) if n%d==0])
        result = search(284987, 457, 60, degree=8, depth=4)
        self.assertTrue(result['short'])
        self.assertEqual(result['divisors'], [521, 547])

    def test_factor_in_denominator_is_separate_from_a_window_hit(self):
        for n in (15, 21):
            result = search(n, 27, 8, degree=5, depth=2)
            self.assertFalse(result['short'])
            self.assertEqual(result['divisors'], [])
            self.assertEqual(n % result['denominator_factor'], 0)
