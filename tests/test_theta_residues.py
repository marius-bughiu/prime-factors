import unittest

from experiments.theta_residues import coefficient_mod


class ThetaResidueTests(unittest.TestCase):
    def test_series_agrees_with_divisor_sum(self):
        # These include primes, prime powers, multiples of five and mixed-sign products.
        for n in range(1, 301):
            with self.subTest(n=n):
                expected = sum(d for d in range(1, n + 1) if n % d == 0 and d % 5 in (1, 4))
                self.assertEqual(coefficient_mod(n, 16), expected % 16)
