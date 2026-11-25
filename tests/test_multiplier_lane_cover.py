import unittest
from math import prod

from experiments.multiplier_lane_cover import multiplier_lanes, run, scale_exponent, signed_log_three
from experiments.newton_lanes import coprime_factorials


class MultiplierLaneCoverTest(unittest.TestCase):
    def test_swapped_and_signed_vertices_include_fixed_endpoints(self):
        for exponent in range(3, 8):
            radix = 1 << exponent
            for n in (1, 5, 7, 11, 13, 17):
                k = signed_log_three(n, exponent)
                self.assertIn(pow(3, k, radix), (n % radix, -n % radix))

                def vertex(u):
                    w = n * pow(u, -1, radix) % radix
                    return min(u % radix, -u % radix, w, -w % radix)

                vertices = {vertex(u) for u in range(1, radix, 2)}
                fixed = [i for i in range(radix//4) if (2*i-k) % (radix//4) == 0]
                self.assertEqual(len(fixed), 0 if k%2 else 2)
                self.assertEqual(len(vertices), radix//8 + 1 - k%2)
                count, anchors = multiplier_lanes(n, exponent)
                covered = set()
                for u in anchors:
                    covered.add(vertex(u))
                    covered.add(vertex(u*pow(3, -1, radix)))
                self.assertEqual(covered, vertices)
                self.assertEqual(count, (len(vertices)+1)//2)

    def test_two_bases_recover_all_original_factor_pairs(self):
        for basis in ('taylor', 'newton'):
            for t in (1, 3):
                self.assertEqual(run(1225, 4, t, basis)['pairs'], [['25','49'], ['35','35']])
                self.assertEqual(run(43657, 2, t, basis)['pairs'], [['149','293']])

    def test_scale_certificate_matches_direct_integer_inequalities(self):
        for m in (1, 2, 3, 4, 8):
            d, h = 2*m+1, m*(m+1)
            for t in (1, 3):
                for basis in ('taylor', 'newton'):
                    div = prod(coprime_factorials(t, 2*m))**2 if basis == 'newton' else 1
                    rhs = d**d * 2**(m*d+2049*h) * t**(2*h)
                    exponent = scale_exponent(m, t, basis)
                    self.assertLess(rhs, div * 2**(exponent*2*m*d))
                    self.assertGreaterEqual(rhs, div * 2**((exponent-1)*2*m*d))
