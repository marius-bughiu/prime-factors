import unittest
from itertools import combinations
from math import gcd, isqrt

from experiments.four_square_lines import chart_rows, search, triples


class FourSquareLineTests(unittest.TestCase):
    def test_determinant_and_row_collisions_on_every_nonnegative_representation_of_77(self):
        # The norm-77 seed (0, 2, 3, 8) gives the chart (4, 37).
        data = []
        for a, b, c, remainder in triples(77):
            d = isqrt(remainder)
            if d*d != remainder:
                continue
            x = a, b, c, d
            matrix = chart_rows((4, 37), x, 77)
            (w, y), (z, t) = matrix
            self.assertEqual((w*t-z*y) % 77, 0)
            data.append((x, matrix))
        for (x, m), (y, k) in combinations(data, 2):
            a, b, c, d = x
            w, i, j, u = y
            # Coordinates of x * conjugate(y), independently of the chart.
            coords = (a*w+b*i+c*j+d*u, -a*i+b*w-c*u+d*j,
                      -a*j+b*u+c*w-d*i, -a*u-b*j+c*i+d*w)
            # A common kernel is equivalent to all cross-row minors vanishing.
            minors = [s*v-t*r for s, t in m for r, v in k]
            self.assertEqual(gcd(77, *coords), gcd(77, *minors))

    def test_collision_and_one_triple_short(self):
        short = search(667, 247)
        self.assertEqual((short['factor'], short['finite_labels']), (None, 1))
        found = search(667, 248)
        self.assertEqual((found['factor'], found['labels']), (29, [1, 117]))
        self.assertEqual(search(143, 188)['outcome'], 'chart_factor')
        self.assertEqual(search(667, 0)['triples'], 0)
