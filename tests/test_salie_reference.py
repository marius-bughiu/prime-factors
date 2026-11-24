import hashlib
import json
import subprocess
import sys
import unittest
from unittest.mock import call, patch

from experiments import salie_reference as reference


class SalieReferenceTest(unittest.TestCase):
    def test_known_cosines(self):
        for numerator, denominator, doubled in [(0, 1, 2), (1, 6, 1), (1, 4, 0),
                                                 (1, 3, -1), (1, 2, -2), (-1, 3, -1)]:
            low, high = reference.cosine_bounds(numerator, denominator)
            self.assertLessEqual(2*low, doubled*reference.SCALE)
            self.assertLessEqual(doubled*reference.SCALE, 2*high)
            self.assertLess(high-low, reference.SCALE >> 100)

    def test_known_factor_producer_and_factor_blind_replay(self):
        p, q = reference.fixture()
        with patch("builtins.pow", wraps=pow) as exponentiate:
            payload, audit = reference.produce_readings(p, q)
        self.assertEqual(exponentiate.call_args_list.count(call(p, -1, q)), 1)
        self.assertEqual(set(payload), {"n", "readings"})
        self.assertEqual(len(payload["readings"]), 89)
        digest = hashlib.sha256("\n".join(payload["readings"]).encode()).hexdigest()
        self.assertEqual(digest, "7f77431ca3f444d1afa0789d6462840f0d4ec7a1961b51b2e8f5940430ac598d")
        self.assertGreater(audit["min_rounding_margin_units"], 0)
        self.assertLess(audit["max_enclosure_width_units"], reference.SCALE >> 100)

        # Reuse the same observed bytes both locally and in a fresh interpreter
        # that cannot inherit memory containing the producing prime pair.
        encoded = json.dumps(payload)
        with patch.object(reference, "fixture", side_effect=AssertionError), \
             patch.object(reference, "produce_readings", side_effect=AssertionError):
            observed = json.loads(encoded)
            result = reference.decode_readings(int(observed["n"]), observed["readings"])
            with self.assertRaises(ValueError):
                reference.decode_readings(int(observed["n"]), observed["readings"][::-1])
        replay = subprocess.run([sys.executable, reference.__file__, "--decode"],
                                input=encoded, text=True, capture_output=True, check=True)
        self.assertEqual(json.loads(replay.stdout), result)
        self.assertEqual(result["factor"], min(p, q))
        self.assertEqual(result["certified_phase_cells"], 89)
        self.assertEqual(result["crt_updates"], 178)
