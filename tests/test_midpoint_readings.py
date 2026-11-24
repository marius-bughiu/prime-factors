from math import isqrt
import unittest
from unittest.mock import patch

from experiments.midpoint_readings import reading, search


def small_sign_oracle(discriminant, seed):
    """Factor the small seed and enumerate square residues at its odd primes."""
    sign = 1
    remaining = seed
    prime = 2
    while remaining > 1:
        if prime * prime > remaining:
            prime = remaining
        while remaining % prime == 0:
            remaining //= prime
            if prime != 2 and discriminant % prime:
                if all(x*x % prime != discriminant % prime for x in range(1, prime)):
                    sign = -sign
        prime += 1
    return sign


def direct_midpoint_discriminants(n):
    return [h*h-n for h in range(1, 2*isqrt(n)+2)
            if h*h > n and 8*h*h <= 9*n and (2*h-n-1) % 4 == 0]


class MidpointReadingTests(unittest.TestCase):
    def test_sign_against_factored_seed(self):
        seeds = [*range(1, 129), 2**10 * 3**5 * 7, 5**4 * 11**3]
        for d in range(1, 82):
            for seed in seeds:
                self.assertEqual(reading(d, seed), small_sign_oracle(d, seed), (d, seed))

    def test_square_sign_including_shared_prime_powers(self):
        for x in (1, 2, 3, 6, 15, 35, 105):
            for seed in (1, 16, 3**8, 2**8 * 3**5 * 5**3 * 7 * 11):
                self.assertEqual(reading(x*x, seed), 1, (x, seed))

    def test_search_matches_direct_factor_and_midpoint_enumeration(self):
        primes = [p for p in range(3, 100, 2) if all(p % d for d in range(2, isqrt(p)+1))]
        products = [p*q for p in primes for q in primes if p < q <= 2*p]
        for n in products + [3, 251, 10007]:
            expected = [(p, n//p) for p in range(2, isqrt(n)+1)
                        if n % p == 0 and n//p <= 2*p]
            midpoint_count = len(direct_midpoint_discriminants(n))
            for tests in (0, 3):
                with self.subTest(n=n, tests=tests):
                    result = search(n, tests, 17)
                    self.assertEqual(result['pairs'], expected)
                    self.assertEqual(result['midpoints'], midpoint_count)
                    counts = result['survivors']
                    self.assertEqual(len(counts), tests+1)
                    self.assertEqual(counts[0], midpoint_count)
                    self.assertEqual(counts, sorted(counts, reverse=True))
                    self.assertEqual(result['evaluations'], sum(counts[:-1]))
                    self.assertEqual(result['final_square_tests'], counts[-1])
                    if tests == 0:
                        self.assertEqual(result['evaluations'], 0)
                        self.assertEqual(result['final_square_tests'], midpoint_count)

    def test_nonpositive_reading_inputs(self):
        for d, seed in ((0, 1), (1, 0), (-1, 3), (3, -1)):
            with self.assertRaises(ValueError):
                reading(d, seed)

    def test_exact_stage_counts_including_empty_final_stage(self):
        seeds = (6, 15, 35, 77)
        for n in (10007, 257*379):
            remaining = direct_midpoint_discriminants(n)
            expected_counts = [len(remaining)]
            for seed in seeds:
                remaining = [d for d in remaining if small_sign_oracle(d, seed) == 1]
                expected_counts.append(len(remaining))
            with patch('experiments.midpoint_readings.Random.getrandbits',
                       side_effect=[seed-1 for seed in seeds]):
                result = search(n, len(seeds), 17)
            self.assertEqual(result['survivors'], expected_counts)
            self.assertEqual(result['evaluations'], sum(expected_counts[:-1]))
            self.assertEqual(result['final_square_tests'], 0 if n == 10007 else 1)
