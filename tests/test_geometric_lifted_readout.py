import unittest
from math import gcd, isqrt, prod

from experiments.geometric_lifted_readout import search
from experiments.geometric_sum_readout import coefficients


class GeometricLiftedReadoutTests(unittest.TestCase):
    def test_signed_directions_use_one_grid(self):
        cases = [(33127, 13, 'minus_one_gcd', 1), (33127, 2, 'linear_sum', 2),
                 (33127, 12, 'quadratic_coefficient_gcd', 3),
                 (34393, 23, 'quadratic_quotient_gcd', 3),
                 (30353, 22, 'equal_quotient_sum', 3)]
        for n, g, expected, samples in cases:
            run = search(n, g, 128)
            eager = search(n, g, 128, all_targets=True)
            self.assertEqual((run['outcome'], run['factor']), (expected, eager['factor']))
            self.assertEqual(run['outcome'], eager['outcome'])
            self.assertEqual(run['block_work']['root_polynomials'], 1)
            self.assertEqual(run['work']['setup_powers'], 2)
            self.assertEqual(run['block_work']['scalar_products'], samples)
            self.assertEqual(eager['block_work']['scalar_products'], 3)
            c, lin, quad = coefficients(n, run['reduced_base'], run['reduced_target'],
                                        int(run['total_terms']))
            self.assertEqual(run['constant'], c)
            self.assertEqual(run['linear_minus'], lin[2])
            if samples > 1:
                self.assertEqual(run['linear'], lin)
            if samples == 3:
                self.assertEqual(run['quadratic'], quad)
            else:
                self.assertIsNone(run['quadratic'])

    def test_simple_target_does_not_require_cubic_vanishing(self):
        n, base, lower, count = 33127, 2, 365, 22
        modulus = n**3
        lifted = pow(base, n, modulus)
        target = pow(lifted, n+1-lower, modulus)
        raw = prod(target - pow(lifted, i, modulus) for i in range(count)) % modulus
        self.assertEqual(raw, 28035*n*n)
        self.assertEqual(search(n, base, 16)['winning_index'], 3)

    def test_order_and_raw_samples_on_small_balanced_inputs(self):
        primes = [p for p in range(3, 100, 2) if all(p%d for d in range(3, isqrt(p)+1, 2))]
        for p in primes:
            for q in primes:
                if not p < q <= 2*p:
                    continue
                n = p*q
                cap = 32
                for g in (2, n-1):
                    run = search(n, g, cap)
                    count = int(run['total_terms'])
                    origin = int(run['origin'])
                    h = n**3
                    lifted = pow(g, n, h)
                    target = pow(lifted, n+1-origin, h)
                    for key, sample in run['samples'].items():
                        z = int(key)
                        scalar = 1
                        for j in range(count):
                            scalar = scalar*(target*(1+z*n)-pow(lifted*(1+n), j, h)) % h
                        self.assertEqual(sample, scalar)
                    for prime in (p, q):
                        original = [i for i in range(count)
                                    if pow(g, i, prime) == pow(g, n+1-origin, prime)]
                        actual = [i for i in range(count) if pow(lifted, i, prime) == target%prime]
                        self.assertEqual(original, actual)
                        for i in actual:
                            self.assertEqual(pow(lifted, i, prime**2), target%(prime**2))
                    if run['factor'] is not None:
                        self.assertIn(run['factor'], (p, q))

    def test_caps_precede_lift_and_composite_controls_remain_sound(self):
        run = search(104757924493, 2, 198)
        self.assertEqual(run['outcome'], 'block_width_limit')
        self.assertEqual(run['work']['setup_powers'], 0)
        self.assertNotIn('block_work',run)
        self.assertEqual(search(77, 7, 0)['factor'], 7)
        self.assertEqual(search(33127, 33126, 16)['outcome'], 'vanishing_quadratic')
        for n in range(9, 120, 2):
            for g in range(2, min(8,n)):
                r = search(n, g, 64)
                if r['factor'] is not None:
                    self.assertTrue(1 < r['factor'] < n)
                    self.assertEqual(gcd(n, r['factor']), r['factor'])
