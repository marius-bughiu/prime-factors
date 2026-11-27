import json
from math import gcd
import unittest

from experiments.divisor_weight_sectors import ROOT, choose, in_sector
from experiments.rectangular_root_windows import bounds


class DivisorWeightSectorTests(unittest.TestCase):
    def test_public_construction_reproduces_whole_family_parameters(self):
        for row in json.loads((ROOT / "research/divisor-weight-sectors.json").read_text()):
            family = {key: int(value) for key, value in row["family"].items()}
            n, low, high = family["N"], family["L"], family["U"]
            result, height, steps = choose(n, low, high)
            self.assertEqual(result, family)
            self.assertEqual(height, bounds(n, 1)[0])
            self.assertEqual(steps, row["continued_fraction_steps"])
            for i in (0, family["count"] // 2, family["count"] - 1):
                a = family["A"] + 2 * i * family["V"]
                b = family["B"] + 2 * i * family["W"]
                error = 2 * family["H"]
                self.assertEqual(gcd(a, b), 1)
                self.assertEqual((a % 2, b % 2), (1, 1))
                self.assertLessEqual(a * b, family["K"])
                self.assertLessEqual((a * low + error) * low, b * n)
                self.assertLessEqual(b * n + error * high, a * high**2)

    def test_sector_pass_and_fail_against_direct_divisors(self):
        counts = dict(rejected=0, passed_with_witness=0, passed_without_witness=0)
        for n in (77, 143, 221, 323):
            divisors = [p for p in range(1, n + 1) if n % p == 0]
            for low in range(3, 19, 2):
                high = low + 3
                if any(low <= p <= high for p in divisors):
                    continue
                for a in range(1, 12, 2):
                    for b in range(1, a + 1, 2):
                        if gcd(a, b) != 1:
                            continue
                        for h in (1, 3, 5):
                            witness = any(abs(a*p - b*(n//p)) <= 2*h for p in divisors)
                            if in_sector(n, 2*h, low, high, a, b):
                                self.assertFalse(witness)
                                counts["rejected"] += 1
                            else:
                                counts["passed_with_witness" if witness
                                       else "passed_without_witness"] += 1
        self.assertTrue(all(counts.values()), counts)

    def test_one_assignment_can_fail_at_a_winning_multiplier(self):
        n = 34_361_588_549
        self.assertFalse(any(n % d == 0 for d in range(131_976, 132_184)))
        self.assertEqual(65 * 33, 55 * 39)
        x, y = 302, 8_585_197
        self.assertEqual(y * y - x * x, 65 * 33 * n)
        self.assertEqual((y - x, y + x), (55 * 156_089, 39 * 220_141))
        self.assertEqual(gcd(n, y - x), 156_089)
