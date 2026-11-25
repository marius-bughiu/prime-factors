from collections import Counter
from math import gcd, isqrt
import unittest

from experiments.hex_weight_interval import choose_slope_radix, cube_threshold, slope_count, weight_interval
from experiments.midpoint_slope_batches import search
from experiments.midpoint_weights import choose_radix
from experiments.short_basis_sieve import reduced_lattice_basis


class HexWeightTests(unittest.TestCase):
    def test_four_gauss_directions_match_eight_and_exhaustive_search(self):
        for height, gap in ((1, 3), (1, 30), (3, 10), (5, 25)):
            g = 2*gap

            def width(pair):
                a, b = pair
                return max(g*abs(a-b), height*abs(a+b)+(g-3*height)*abs(a-b))

            def transformed(pair):
                a, b = pair
                z, v = height*(a+b), g*(a-b)
                return z+v, z-v

            for radix in range(2, 34):
                if radix**3 <= cube_threshold(height, g):
                    continue
                for s in range(radix):
                    a, b, left, right = weight_interval(radix, s, 100, 100+height, gap, Counter())
                    self.assertEqual(width((a, b)), right-left)
                    (x, y), (z, t) = reduced_lattice_basis(radix, s, transformed, Counter())
                    combinations = ((1, 0), (0, 1), (1, 1), (1, -1), (2, 1), (2, -1), (1, 2), (1, -2))
                    eight = min(width((i*x+j*z, i*y+j*t)) for i, j in combinations)
                    bound = eight//(2*height)
                    best = min(width((u, v)) for u in range(-bound, bound+1)
                               for v in range(-bound+(s*u+bound) % radix, bound+1, radix) if u or v)
                    self.assertEqual(width((a, b)), eight)
                    self.assertEqual(width((a, b)), best)

    def test_threshold_and_slope_count_at_the_selected_radix(self):
        for n in range(301, 8000, 26):
            height, gap_width = isqrt(9*n//8)-isqrt(n-1)-1, 2*isqrt(n//8)
            old = choose_radix(n, 4*height*gap_width)
            for multiplier in (1, 2):
                new = choose_slope_radix(n, height, gap_width, Counter(), multiplier)
                self.assertLess(4*height*gap_width**2, (gap_width+3*height)*new**3)
                self.assertEqual(gcd(new, n), 1)
                self.assertLessEqual(slope_count(multiplier*new, Counter()),
                                     slope_count(multiplier*old, Counter()))

    def test_all_integer_balanced_pairs_on_small_products(self):
        for n in range(3, 2001, 2):
            expected = [[str(x), str(n//x)] for x in range(2, isqrt(n)+1)
                        if n % x == 0 and n//x <= 2*x]
            for geometry in ('hexagon', 'hexagon_slope'):
                for curve in (False, True):
                    got = search(n, geometry=geometry, curve=curve)
                    self.assertEqual(got['pairs'], expected, (n, geometry, curve))
                    self.assertEqual(got['remaining_orbits'], 0)
