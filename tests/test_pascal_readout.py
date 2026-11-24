from math import comb, isqrt
from unittest import TestCase
from unittest.mock import patch

from experiments.pascal_readout import search


class PascalReadoutTests(TestCase):
    def test_prime_pairs_and_odd_cutoffs(self):
        primes = [p for p in range(3, 65, 2) if all(p % d for d in range(2, isqrt(p)+1))]
        for p in primes:
            for q in primes:
                if not p < q < 4*p:
                    continue
                n = p*q
                for k in range(1, 2*p, 2):
                    expected = n-1 if k < p else q-1 if k < q else p+q-1
                    self.assertEqual(comb(n-1, k) % n, expected, (p, q, k))
                self.assertEqual(search(n, 'sqrt', 256)['factor'], q)
                if p.bit_length() == q.bit_length():
                    self.assertEqual(search(n, 'dyadic', 256)['factor'], p)

    def test_budget_stops_before_constructing_coefficient(self):
        with patch('experiments.pascal_readout.comb', side_effect=AssertionError):
            result = search(143, 'sqrt', 10)
        self.assertEqual(result['index'], '11')
        self.assertEqual(result['coefficients_evaluated'], 0)
        self.assertIsNone(result['factor'])
        self.assertEqual(search(143, 'sqrt', 11)['factor'], 13)

    def test_outside_promise_checks_discovered_divisor(self):
        for n in (3, 17, 81, 3*53, 3*5*11):
            for method in ('sqrt', 'dyadic'):
                factor = search(n, method, 32)['factor']
                if factor is not None:
                    self.assertTrue(1 < factor < n and n % factor == 0)
