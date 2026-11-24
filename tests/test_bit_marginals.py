import subprocess
import unittest
from pathlib import Path

from experiments.bit_marginals import Tape, discover, run_fixtures


ROOT = Path(__file__).resolve().parents[1]


class BitMarginalTests(unittest.TestCase):
    def test_balanced_width_from_product_alone(self):
        result = discover(95)
        self.assertEqual(result["width"], 4)
        # 95 = 5*19 lies outside this balanced search box.
        self.assertEqual(result["count_mod3"], 0)
        result = discover(143)
        self.assertEqual(result["factors"], ["11", "13"])

    def test_zero_intermediate_has_nonzero_derivative(self):
        # 1 + (1 + 1 + z) * w. At z=w=1 the parenthesis vanishes over F_3.
        tape = Tape(2)
        z, w = tape.tags
        inner = tape.gate("+", tape.gate("+", 1, 1), z)
        root = tape.gate("+", 1, tape.gate("*", inner, w))
        value, gradient, _, zero_gates = tape.differentiate_at_one(root)
        self.assertEqual((value, gradient), (1, [1, 0]))
        self.assertGreater(zero_gates, 0)

    def test_zero_intermediate_in_multiplier(self):
        # In the wider box the first inputs are 1, 2, 3 and 6. The bit counts
        # are 2, 3 and 1, so the middle derivative vanishes in the field.
        result = discover(6, 3)
        self.assertEqual(result["count_mod3"], 1)
        self.assertEqual(result["marginals"], [2, 0, 1])
        self.assertGreater(result["zero_gates_with_adjoint"], 0)

    def test_all_tiny_product_outputs(self):
        # Exhaustive multiplication serves only as an independent test oracle.
        for width in range(1, 4):
            bound = 1 << width
            for n in range(1, bound * bound):
                with self.subTest(width=width, n=n):
                    result = discover(n, width)
                    first_inputs = [x for x in range(bound) for y in range(bound) if x * y == n]
                    self.assertEqual(result["count_mod3"], len(first_inputs) % 3)
                    expected = [sum((x >> i) & 1 for x in first_inputs) % 3 for i in range(width)]
                    self.assertEqual(result["marginals"], expected)

    def test_bounded_fixture_certificates(self):
        proofs = ["import Mathlib.Data.Nat.Prime.Basic"]
        for result in run_fixtures():
            if result["factors"]:
                p, q = result["factors"]
                proofs.append(f"example : ({result['n']} : ℕ) = {p} * {q} ∧ "
                              f"Nat.Prime {p} ∧ Nat.Prime {q} := by decide +kernel")
        subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT,
                       input="\n".join(proofs), text=True, check=True)
