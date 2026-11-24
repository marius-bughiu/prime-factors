import json
import unittest
from pathlib import Path

from experiments.partition_recurrence import logarithmic_prefix, search
from experiments.theta_residues import coefficient_mod


class PartitionRecurrenceTests(unittest.TestCase):
    def test_two_theta_series_all_indices(self):
        # Multiples of five belong to both products and matter at intermediate indices.
        for residue in (1, 2):
            for modulus in (2, 4, 8, 9, 32):
                values, updates, possible = logarithmic_prefix(400, modulus, residue)
                expected = [sum(d for d in range(1, n + 1)
                                if n % d == 0 and d % 5 in (0, residue, 5 - residue)) % modulus
                            for n in range(401)]
                self.assertEqual(values, expected)
                self.assertLess(updates, possible)

    def test_independent_partition_sum_at_matching_precision(self):
        for n in (143, 667, 1457, 1537):
            result = search(n, 1537)
            for modulus in (1 << ((n.bit_length() + 3) // 4), result['modulus']):
                values, _, _ = logarithmic_prefix(n, modulus)
                self.assertEqual(values[n], coefficient_mod(n, modulus))

    def test_odd_prime_powers_force_zero(self):
        # Three odd-exponent primes away from five force zero modulo four.
        # Replacing two exponents by an even exponent must not trigger that inference.
        n = 3 * 7 * 11
        values, _, _ = logarithmic_prefix(10 * n, 4)
        for scale in (1, 2, 5, 10):
            self.assertEqual(values[n * scale], 0)
        self.assertNotEqual(values[3 * 7**2], 0)
        # At the active threshold, two primes 13 mod 20 give exactly one power of two.
        self.assertEqual(values[13 * 53], 2)

    def test_public_cases(self):
        path = Path(__file__).resolve().parents[1] / 'benchmarks' / 'partition-recurrence.json'
        for case in json.loads(path.read_text()):
            result = search(int(case['n']), case['max_index'])
            factor = result.pop('factor')
            for key, value in result.items():
                self.assertEqual(value, case[key], (case['id'], key))
            if factor is not None:
                self.assertEqual(sorted((factor, int(case['n']) // factor)),
                                 list(map(int, case['factors'])))
            else:
                self.assertEqual(case['remaining'], [case['n']])


if __name__ == '__main__':
    unittest.main()
