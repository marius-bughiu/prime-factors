import json
from math import isqrt, prod
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from scripts.factor import discover, fermat_split, prime_witness, render_certificate


REPO = Path(__file__).resolve().parents[1]


class FactorTests(unittest.TestCase):
    def test_pinned_results(self):
        for case in json.loads((REPO / "benchmarks/cases.json").read_text()):
            with self.subTest(case=case["id"]):
                n = int(case["n"])
                factors, remaining, steps = discover(n, case["max_steps"], [])
                self.assertEqual(factors, list(map(int, case["factors"])))
                self.assertEqual(remaining, list(map(int, case["remaining"])))
                self.assertEqual(steps, case["fermat_steps"])
                self.assertEqual(prod(factors) * prod(remaining), n)
                if not remaining:
                    self.assertIn("theorem factorization", render_certificate(n, factors))

    def test_midpoint_window(self):
        # Exhaustive finite check against the factor-pair description of the window.
        for n in range(3, 300, 2):
            start = isqrt(n - 1) + 1
            for budget in (0, 1, 3, 8):
                candidates = [p for p in range(2, isqrt(n) + 1)
                              if n % p == 0 and (p + n // p) // 2 < start + budget]
                actual, steps = fermat_split(n, budget)
                self.assertEqual(actual, max(candidates, default=None), (n, budget))
                self.assertLessEqual(steps, budget)

    def test_composite_hint_needs_further_splits(self):
        n = 101 * 103 * 10007
        self.assertEqual(discover(n, 1, [101 * 103]), ([101, 103, 10007], [], 1))
        with self.assertRaises(ValueError):
            discover(n, 1, [37])
        with self.assertRaises(ValueError):
            render_certificate(n, [n])

    def test_one_partial_and_invalid(self):
        self.assertEqual(discover(1, 0, []), ([], [], 0))
        self.assertEqual(discover(2 * 101 * 103, 0, []), ([2], [10403], 0))
        with self.assertRaises(ValueError):
            discover(0, 0, [])
        with self.assertRaises(ValueError):
            discover(1, -1, [])
        with self.assertRaises(ValueError):
            render_certificate(15, [3])

    def test_pseudoprime_does_not_get_certificate(self):
        for n in (341, 2047, 561, 3215031751, 3825123056546413051):
            self.assertIsNone(prime_witness(n))

    def test_subgroup_cli_discovers_then_certifies_its_split(self):
        p = 223 * 2**512 + 1
        q = 1197 * (p - 1) + 1
        with tempfile.TemporaryDirectory() as temp:
            proof = Path(temp) / "Proof.lean"
            cmd = [sys.executable, str(REPO / "scripts/factor.py"), str(p * q),
                   "--method", "subgroup", "--max-base", "2", "--max-steps", "0",
                   "--lean", str(proof)]
            result = subprocess.run(cmd, cwd=temp, capture_output=True, text=True, check=True)
            report = json.loads(result.stdout)
            self.assertEqual(report["factors"], [str(p), str(q)])
            self.assertEqual(report["subgroup"]["witness_base"], 2)
            self.assertEqual(report["fermat_steps"], 0)
            self.assertIn(f"ExactFactorization {p * q}", proof.read_text())

    def test_partial_preserves_existing_certificate(self):
        with tempfile.TemporaryDirectory() as temp:
            proof = Path(temp) / "Proof.lean"
            proof.write_text("earlier proof")
            cmd = [sys.executable, str(REPO / "scripts/factor.py"), "10403",
                   "--max-steps", "0", "--lean", str(proof)]
            result = subprocess.run(cmd, capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)
            self.assertFalse(json.loads(result.stdout)["verified"])
            self.assertEqual(proof.read_text(), "earlier proof")


if __name__ == "__main__":
    unittest.main()
