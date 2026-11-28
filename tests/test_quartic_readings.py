import json
from math import isqrt
import unittest
from unittest.mock import patch

from experiments.quartic_readings import FIXTURE, read_product, verify_case


class QuarticReadingsTests(unittest.TestCase):
    def test_fixture_replay_and_root_counts(self):
        cases = json.loads(FIXTURE.read_text())
        self.assertEqual(len(cases), 5)
        for case in cases:
            with self.subTest(case=case["id"]):
                with patch("experiments.quartic_product_strips.isqrt", wraps=isqrt) as roots:
                    result = verify_case(case)
                self.assertEqual(result["recognizer_isqrts"], roots.call_count)
                self.assertEqual(roots.call_count, 24)
                self.assertEqual(result["remaining"], [] if case["factors"] else [case["n"]])
                if result["factors"]:
                    p, q = map(int, result["factors"])
                    # Check the inclusive rank by its defining square inequalities.
                    n = int(case["n"])
                    start = (p + q) // 2 + 1 - int(case["fermat_rank"])
                    self.assertLess((start - 1)**2, n)
                    self.assertGreaterEqual(start**2, n)
                    if case["id"] == "quartic-later-midpoint-2048":
                        self.assertTrue(2**719 < int(case["fermat_rank"]) < 2**720)

    def test_forward_branch_and_proper_projection(self):
        self.assertEqual(read_product(151847041), ([(1, "x", (10301, 14741))], 2))
        # The quartic representation of 5 yields (1, 5) on both branches.
        self.assertEqual(read_product(5), ([], 4))


if __name__ == "__main__":
    unittest.main()
