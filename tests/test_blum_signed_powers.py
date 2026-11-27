import json
import unittest

from experiments.blum_signed_powers import ROOT, check, compare_public, report


class BlumSignedPowerTests(unittest.TestCase):
    def test_complete_panel_and_bounded_controls(self):
        self.assertEqual(json.loads(json.dumps(report())),
                         json.loads((ROOT / "research/blum-signed-powers.json").read_text()))

    def test_benchmark_expected_data_are_used_only_for_comparison(self):
        for case in json.loads((ROOT / "benchmarks/blum-signed-powers.json").read_text()):
            n = int(case["n"])
            result = compare_public(n, case["base"], case["budget"])
            self.assertEqual(result, case["checks"])
            hits = result["signed"]["divisors"]
            recovered = sorted((int(hits[0]), n // int(hits[0]))) if hits else []
            self.assertEqual(case["factors"], [str(value) for value in recovered])
            self.assertEqual(case["remaining"], [] if recovered else [str(n)])

    def test_synchronized_return_before_and_at_exact_cutoff(self):
        self.assertEqual(check(71, 79, 3, 11)[2], {"ordinary": None, "signed": None})
        self.assertEqual(check(71, 79, 3, 12)[2],
                         {"ordinary": None, "signed": (12, 71, 79)})
