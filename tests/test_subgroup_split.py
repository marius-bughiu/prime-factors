import json
import math
import unittest
from pathlib import Path

from experiments.subgroup_split import search


class SubgroupSplitTests(unittest.TestCase):
    def test_curated_large_inputs_are_products_of_proth_primes(self):
        path = Path(__file__).resolve().parents[1] / "benchmarks/subgroup.json"
        cases = {case["id"]: case for case in json.loads(path.read_text())}
        power = 2**512
        p = 223 * power + 1
        for odd_part, base in ((223, 3), (1197 * 223, 5), (266085, 7)):
            self.assertTrue(odd_part % 2 == 1 and 0 < odd_part < power)
            proth = odd_part * power + 1
            self.assertEqual(pow(base, (proth - 1) // 2, proth), proth - 1)
        control_q = 266085 * power + 1
        self.assertNotEqual((control_q - 1) % (p - 1), 0)
        control = cases["subgroup-1050-control"]
        self.assertEqual(int(control["n"]), p * control_q)
        self.assertEqual(int(cases["subgroup-1050"]["n"]), p * (1197 * (p - 1) + 1))
        result = search(int(control["n"]), control["max_base"])
        self.assertEqual((result["status"], result["bases_tested"]), ("exhausted", 64))

    def test_widely_spaced_proth_primes(self):
        p = 223 * 2**512 + 1
        q = 1197 * (p - 1) + 1
        n = p * q
        result = search(n)
        self.assertEqual(result["witness_kind"], "power_gcd")
        self.assertEqual(result["bases_tested"], 1)
        self.assertEqual(result["witness_base"], 2)
        self.assertEqual(result["max_base"], n.bit_length() ** 2)
        residue = pow(result["witness_base"], n - 1, n)
        self.assertEqual(int(result["residue"]), residue)
        self.assertEqual(math.gcd(residue - 1, n), p)
        self.assertEqual((int(result["factor"]), int(result["cofactor"])), (p, q))

    def test_direct_gcd_and_inclusive_cap(self):
        self.assertEqual(search(26, 1)["status"], "exhausted")
        result = search(26, 2)
        self.assertEqual(result["witness_kind"], "base_gcd")
        self.assertEqual(result["factor"], "2")
        self.assertNotIn("residue", result)

    def test_prime_and_composite_can_both_exhaust(self):
        for n in (2, 17, 35):
            report = search(n, 2)
            self.assertEqual(report["status"], "exhausted")
            self.assertNotIn("factor", report)
            self.assertEqual(report["bases_tested"], int(n > 2))

    def test_invalid_inputs(self):
        for n, cap in ((1, None), (-3, None), (23, 0)):
            with self.assertRaises(ValueError):
                search(n, cap)


if __name__ == "__main__":
    unittest.main()
