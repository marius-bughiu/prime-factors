from collections import Counter
from math import gcd, prod
import unittest

from experiments.geometric_readout_blocks import _scalar_family, _shape, blocked_coefficients, search
from experiments.geometric_sum_readout import coefficients, search as direct_search


class GeometricBlockTests(unittest.TestCase):
    def test_scalar_family_against_every_original_factor(self):
        for mod, base in [(9**3, 1), (15**3, 2), (25**3, 4), (13**3, 12)]:
            for count in [1, 2, 8, 16, 17, 30, 63, 100, 181]:
                width, groups, tail = _shape(count)
                targets = [0, base**2 % mod, mod-1]
                work = Counter()
                blocked = _scalar_family(base, targets, mod, width, groups, tail, work)
                for y, value in zip(targets, blocked):
                    self.assertEqual(value, prod(y-pow(base,j,mod) for j in range(count)) % mod)
                self.assertEqual(work['grid_inversions'], 1)
                self.assertEqual(work['block_evaluations'], 3*groups)

    def test_every_coefficient_with_composite_moduli_and_repeated_points(self):
        for n in [9, 15, 21, 77, 101]:
            for g in [1, 2, 4, n-1]:
                for y in [0, 1, 3, n-1]:
                    for count in [0, 1, 3, 16, 29, 63]:
                        readings, _ = blocked_coefficients(n, g, y, count)
                        self.assertEqual(readings, coefficients(n, g, y, count))
        with self.assertRaises(ValueError):
            blocked_coefficients(15, 3, 1, 5)

    def test_fresh_control_and_shared_decoder(self):
        from experiments.affine_radix_holdout import draw_prime
        primes = [draw_prime(side, 1, bits=19, seed=b'geometric-block-readout-v1')
                  for side in (b'p', b'q')]
        fresh = prod(primes)
        self.assertEqual(fresh, 104757924493)
        for n, g in [(30353, 22), (34393, 23), (33127, 12), (fresh, 2)]:
            b = search(n, g, 200)
            direct = direct_search(n, g, 50000)
            for key in ['constant', 'linear', 'quadratic', 'outcome', 'factor',
                        'winning_index', 'equal_hits', 'quotient_hits']:
                self.assertEqual(b[key], direct[key])
            self.assertEqual(gcd(n, b['factor']), b['factor'])
            self.assertGreater(b['factor'], 1)
        stats = b['block_work']
        self.assertEqual(stats['scalar_products'], 7)
        self.assertEqual(stats['baby_roots'], 3*199)
        self.assertEqual(stats['block_evaluations'], 7*197)
        self.assertEqual(stats['tail_terms'], 7*64)
        self.assertEqual(stats['block_width']*stats['blocks_per_scalar']+stats['tail_per_scalar'],
                         int(b['total_terms']))

    def test_cap_and_setup_factor(self):
        b = search(104757924493, 2, 198)
        self.assertEqual(b['outcome'], 'block_width_limit')
        self.assertEqual(b['work']['unvisited_terms'], 39267)
        self.assertNotIn('block_work', b)
        self.assertEqual(b['work']['modular_powers'], 0)
        self.assertEqual(search(77, 7, 0)['factor'], 7)
        self.assertEqual(search(13, 2, 0)['outcome'], 'no_product_hit')


class GeometricAdaptiveTests(unittest.TestCase):
    def test_linear_paths_do_not_measure_quadratic_values(self):
        for base, expected in [(2, 'linear_sum'), (13, 'linear_gcd')]:
            reference = search(33127, base, 16)
            for mode, counts in [('cube_first', (0, 3)), ('square_first', (3, 0))]:
                adaptive = search(33127, base, 16, mode=mode)
                self.assertEqual(adaptive['outcome'], expected)
                self.assertEqual(adaptive['factor'], reference['factor'])
                self.assertEqual(adaptive['linear'], reference['linear'])
                self.assertIsNone(adaptive['quadratic'])
                ops = adaptive['block_work']
                self.assertEqual((ops['square_products'], ops['cube_products']), counts)
                self.assertEqual(ops['root_polynomials'], 2)
                self.assertEqual(ops['exact_divisions'], 2)

    def test_six_samples_on_quadratic_branches(self):
        for n, base in [(34393, 23), (30353, 22), (33127, 12)]:
            ref = search(n, base, 16)
            for mode, low in [('cube_first', 0), ('square_first', 3)]:
                r = search(n, base, 16, mode=mode)
                for key in ['constant', 'linear', 'quadratic', 'outcome', 'factor',
                            'winning_index', 'quotient_hits', 'equal_hits', 'work']:
                    self.assertEqual(r[key], ref[key])
                ops = r['block_work']
                self.assertEqual(ops['cube_products'], 6)
                self.assertEqual(ops['square_products'], low)
                self.assertEqual(ops['exact_divisions'], 7)
                self.assertEqual(ops['root_polynomials'], 3 if low == 0 else 5)
                self.assertEqual(ops['block_evaluations'], (6+low)*r['blocks_per_scalar'])

    def test_caps_precede_either_precision(self):
        for mode in ['cube_first', 'square_first']:
            r = search(104757924493, 2, 198, mode=mode)
            self.assertEqual(r['outcome'], 'block_width_limit')
            self.assertIsNone(r['linear'])
            self.assertNotIn('block_work', r)
            self.assertEqual(r['work']['modular_powers'], 0)
        with self.assertRaises(ValueError):
            search(33127, 2, 64, mode='unknown')
