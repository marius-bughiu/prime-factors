"""Check the decoder's error allowance separately from direct-sum evaluation."""

from itertools import product
from math import acos, cos, tau
import unittest

from experiments.salie_residues import decode_phases, prime_schedule, projection, search


class SalieResidueTests(unittest.TestCase):
    def test_extreme_measurement_errors(self):
        for n, root in [(221, 118), (667, 231), (1763, 42)]:
            primes = prime_schedule(n)
            for errors in product((-1, 1), repeat=len(primes)):
                phases = []
                for prime, sign in zip(primes, errors):
                    index = root * pow(prime, -1, n) % n
                    measured = cos(tau * index / n) + sign / (64 * prime ** 2)
                    phase = acos(max(-1, min(1, measured))) / tau
                    phases.append((prime, phase))
                with self.subTest(n=n, errors=errors):
                    result = decode_phases(n, phases)
                    self.assertEqual(result["outcome"], "crt_split")
                    self.assertIn(result["root"], (root, n - root))

    def test_projection_is_separate_from_evaluation(self):
        schedule = projection(2048)
        self.assertEqual((schedule["prime_count"], schedule["max_precision_bits"]), (233, 29))
        self.assertTrue(schedule["same_schedule_for_entire_width"])
        limited = search((1 << 2048) - 1, 1000)
        self.assertEqual(limited["outcome"], "size_limit")
        self.assertEqual((limited["unit_gcds"], limited["terms"]), (0, 0))
