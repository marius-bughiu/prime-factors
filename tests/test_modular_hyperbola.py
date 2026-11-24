import json
import unittest
from math import isqrt
from pathlib import Path

from experiments.modular_hyperbola import Work, floor_sum, report_progression, search


class ModularHyperbolaTests(unittest.TestCase):
    def test_decimal_fixtures(self):
        fixtures = Path(__file__).resolve().parents[1] / "benchmarks" / "modular-hyperbola.json"
        for case in json.loads(fixtures.read_text()):
            n = int(case["n"])
            actual = search(n)
            self.assertEqual(actual["pairs"], [case["factors"]] if case["factors"] else [])
            self.assertEqual(actual["low_classes"], case["low_classes"])
            self.assertEqual(actual["modular_hits"], case["modular_hits"])

    def test_floor_sum_with_signed_data(self):
        work = Work()
        for length in range(9):
            for modulus in range(1, 10):
                for a in range(-5, 11):
                    for b in range(-4, 6):
                        expected = sum((a * j + b) // modulus for j in range(length))
                        self.assertEqual(floor_sum(length, modulus, a, b, work), expected)

    def test_progression_intervals(self):
        for modulus in (4, 8):
            for a in range(modulus):
                for b in range(modulus):
                    for l in range(modulus + 1):
                        for h in range(l, modulus + 1):
                            actual = list(report_progression(a, b, modulus, 2, 9, l, h, Work()))
                            points = [(v, (a * v + b) % modulus) for v in range(2, 9)]
                            self.assertEqual(actual, [(v, z) for v, z in points if l <= z < h])

    def test_search_and_modular_hit_count(self):
        for n in range(3, 512, 2):
            xmax = isqrt(n)
            xmin = max(2, isqrt((n - 1) // 2) + 1)
            ymin, ymax = isqrt(n - 1) + 1, isqrt(2 * n)
            width = ymax.bit_length()
            for r in range((width + 1) // 2, width + 1):
                result = search(n, r)
                expected = [[str(x), str(n // x)] for x in range(xmin, xmax + 1) if n % x == 0]
                self.assertEqual(sorted(result["pairs"]), sorted(expected))
                hits = sum((x * y - n) % (1 << (2 * r)) == 0
                           for x in range(xmin, xmax + 1) for y in range(ymin, ymax + 1))
                self.assertEqual(result["modular_hits"], hits)
