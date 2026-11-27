import json
from math import gcd, isqrt
import unittest

from experiments.affine_radix_holdout import draw_prime
from experiments.weighted_global_trace import FIXTURE, check_fixture, compare, run_fixture


class WeightedGlobalTraceTests(unittest.TestCase):
    def test_stored_small_panel_and_independent_draws(self):
        for case in json.loads(FIXTURE.read_text()):
            if case["factor_bits"] > 16:
                continue
            with self.subTest(case=case["id"]):
                if "draw_index" in case:
                    p, q = (draw_prime(side, case["draw_index"], bits=9,
                                       seed=b"weighted-global-trace/v1")
                            for side in (b"p", b"q"))
                    self.assertEqual(p*q, int(case["n"]))
                check_fixture(case, run_fixture(case))

    def test_off_gap_gcd_without_own_gap_or_square(self):
        n = 91787
        report, _ = compare(n, 9, 2, 64, 2)
        match = report["global"]["first_off_gap_factor"]
        a, b = match["weights"]
        s = int(match["sum"])
        h = n // 2
        left = pow(2, s - (h+1)*(a+b), n)
        right = pow(2, h*match["matched_gap"], n)
        self.assertNotEqual(match["matched_gap"], b-a)
        self.assertEqual((left+pow(left, -1, n)) % n, (right+pow(right, -1, n)) % n)
        self.assertEqual(gcd(left-right, n), 349)
        delta = s*s - 4*a*b*n
        self.assertNotEqual(isqrt(delta)**2, delta)
        self.assertEqual(report["square"]["divisors"], [])
        self.assertEqual(report["own"]["divisors"], [])
        self.assertEqual(report["global"]["setup_divisors"], [])

    def test_setup_only_and_zero_budget(self):
        report, _ = compare(43621, 8, 2, 64, 0)
        self.assertEqual(report["global"]["setup_divisors"], ["241"])
        self.assertEqual(report["global"]["scan_powers"], 0)
        self.assertEqual(report["square"]["square_tests"], 0)
        none, _ = compare(43621, 8, 2, 0, 2)
        self.assertEqual(none["global"]["divisors"], [])
        self.assertEqual(none["global"]["setup_powers"], 0)

    def test_scalar_and_inverse_equalities_are_unsuccessful_readouts(self):
        for n, bits, expected in ((215071, 9, "whole"), (25021, 8, "one")):
            report, _ = compare(n, bits, 2, 64, 2)
            self.assertGreater(report["global"]["readouts"][expected], 0)
            for divisor in report["global"]["divisors"]:
                self.assertTrue(1 < int(divisor) < n and n % int(divisor) == 0)
