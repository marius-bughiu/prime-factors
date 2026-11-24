import json
from math import isqrt
from pathlib import Path
import unittest

from experiments.gap_coverage import primes_through
from experiments.polynomial_packet import example_coefficient, search


class PolynomialPacketTests(unittest.TestCase):
    def test_decoded_rows_match_exhaustive_small_inputs(self):
        for n in range(3, 40):
            for coefficient in range(1, 21):
                for height in (0, 1, 4, 13):
                    actual = search(n, coefficient, height, max_lifts=10000)
                    expected = []
                    for m in range(isqrt(n + coefficient * height) + 1):
                        q, rem = divmod(m * m - n, coefficient)
                        if rem == 0 and abs(q) <= height:
                            expected.append([str(m), str(q)])
                    self.assertTrue(actual["interval_complete"])
                    self.assertEqual(actual["rows"], expected, (n, coefficient, height))

    def test_budget_distinguishes_no_lift_and_unchecked_lifts(self):
        empty = search(15, 2, 0, max_lifts=0)
        self.assertTrue(empty["interval_complete"])
        self.assertEqual(empty["euclidean_steps"], 0)
        truncated = search(15, 1, 10, max_lifts=0)
        self.assertFalse(truncated["interval_complete"])
        self.assertEqual(truncated["tested_lifts"], 0)
        self.assertIsNone(truncated["factor"])

    def test_fixed_public_parameters_on_both_2048_bit_products(self):
        path = Path(__file__).resolve().parents[1] / "benchmarks" / "polynomial-packets.json"
        for case in json.loads(path.read_text()):
            n = int(case["n"])
            self.assertEqual(n.bit_length(), 2048)
            self.assertEqual(example_coefficient(), int(case["coefficient"]))
            # Four roots at the power of two, two lifts at each odd prime square.
            self.assertEqual(n % 8, 1)
            local_classes = 4
            for prime in primes_through(173)[1:]:
                self.assertEqual(pow(n, (prime - 1) // 2, prime), 1)
                local_classes *= 2
            self.assertEqual(local_classes, 1 << 41)
            result = search(n, example_coefficient(), 1 << 308)
            self.assertLessEqual(16 * int(result["radius"])**3, example_coefficient())
            for field in ("interval_complete", "radius", "euclidean_steps", "possible_lifts",
                          "tested_lifts", "rows", "square_norms"):
                self.assertEqual(result[field], case[field], (case["id"], field))
            if case["status"] == "complete":
                factor = result["factor"]
                self.assertEqual([str(factor), str(n // factor)], case["factors"])
                self.assertEqual(n % factor, 0)
                fermat_midpoints = (factor + n // factor) // 2 - isqrt(n)
                self.assertEqual(fermat_midpoints.bit_length(), 251)
            else:
                self.assertIsNone(result["factor"])
