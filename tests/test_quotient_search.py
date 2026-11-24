import unittest

from experiments.quotient_search import Strip, Work, search, self_test, wheel_lattices


class QuotientSearchTests(unittest.TestCase):
    def test_moments_and_complete_band(self):
        self_test()

    def test_mixed_moments_in_skew_wheel_coordinates(self):
        n, lo, hi = 667, 19, 25
        for wheel in (2, 3, 6, 10):
            for lattice in wheel_lattices(n, wheel):
                step, a, square, c, d = lattice
                strip = Strip(n, lo, hi, Work(), lattice)
                points = [(x, y) for x in range(lo, hi+1) if (x-a)%step == 0
                          for y in range((n*(2*lo-x)-1)//(lo*lo)+1,
                                         n*(lo+hi-x)//(lo*hi)+1)
                          if (y-c-d*x)%square == 0]
                self.assertEqual(strip.count(), len(points))
                for power in range(4):
                    self.assertEqual(strip.errors(power, 1),
                                     sum(x*(x*y-n)**power for x, y in points))

    def test_wide_cells_can_stop_above_uniform_area(self):
        run = search(140188063, width=24)
        self.assertEqual(run["pairs"], [["10007", "14009"]])
        self.assertEqual(run["collinear_beyond_area"], 8)
        self.assertEqual(run["bisected"], 1)
