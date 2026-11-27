import unittest
from math import isqrt

from experiments.secant_quotient_cells import plan, search, secant_lattices


class SecantQuotientCellsTests(unittest.TestCase):
    def test_full_sweep_against_division(self):
        for n in range(9, 500, 2):
            left = max(2, isqrt((n-1)//2)+1)
            expected = [[str(x), str(n//x)] for x in range(left, isqrt(n)+1) if n % x == 0]
            for wheel in (2, 6, 30):
                for widest in (False, True):
                    with self.subTest(n=n, wheel=wheel, widest=widest):
                        self.assertEqual(search(n, wheel, widest)["pairs"], expected)

    def test_secant_in_every_reduced_class(self):
        for wheel in (2, 6, 10, 30, 210):
            for _, a, vertical, intercept, slope in secant_lattices(1, wheel):
                self.assertEqual(vertical, 2*wheel*wheel)
                for t in range(-wheel, wheel+1):
                    x = a+t*wheel
                    self.assertEqual(x*(intercept+slope*x) % vertical, 1)

    def test_nonunit_setup_does_not_omit_proper_balanced_factor(self):
        result = search(3*5*7*11, 210)
        self.assertEqual(result["setup_divisor"], "105")
        self.assertEqual(result["wheel"], 2)
        self.assertEqual(result["pairs"], [["33", "35"]])

    def test_integer_width_rounding(self):
        for n in (51, 97*193, 3376036549, 1900014700027):
            for widest, coefficient in ((False, 4), (True, 8)):
                left, right, width, wheel, _ = plan(n, 210, widest)
                threshold = coefficient*(wheel*left)**3
                self.assertLess(n*(width-1)**3, threshold)
                if width <= right-left+1:
                    self.assertGreaterEqual(n*width**3, threshold)


if __name__ == "__main__":
    unittest.main()
