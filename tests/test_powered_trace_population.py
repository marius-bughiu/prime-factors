import json
import unittest
from collections import Counter
from fractions import Fraction
from math import gcd

from experiments.powered_trace_population import RECORD, image_counts, report
from experiments.weighted_global_trace import schedule, trace_search


class PoweredTracePopulationTests(unittest.TestCase):
    def test_fixed_powers_against_every_actual_seed(self):
        p, q = 37, 41
        n = p*q
        gaps, coords, _ = schedule(n, 6, 64, 2)
        units = [v for v in range(1, n) if gcd(n, v) == 1]
        wins = Counter()
        outcome = {}
        for v in units:
            result = trace_search(n, v, gaps, coords, True)[0]
            outcome[v] = (bool(result["setup_divisors"]), bool(result["divisors"]))
            if outcome[v] == (False, True):
                r = next(i for i in range(1, p) if pow(v, i, p) == 1)
                t = next(i for i in range(1, q) if pow(v, i, q) == 1)
                wins[r, t] += 1
        known_orders = [(r, t, count) for (r, t), count in wins.items()]
        for e in (0, 1, 2, 14, 64, n-1):
            left, right = (p-1)//gcd(e, p-1), (q-1)//gcd(e, q-1)
            size, pre, extra = image_counts(left, right, [(n-1)*d for d in gaps], known_orders)
            observations = [outcome[pow(v, e, n)] for v in units]
            self.assertEqual(Fraction(pre, size), Fraction(observations.count((True, True)), len(units)))
            self.assertEqual(Fraction(extra, size), Fraction(observations.count((False, True)), len(units)))

    def test_full_size_record(self):
        actual = report()
        self.assertEqual(actual, json.loads(RECORD.read_text()))
        private = actual[0]["rows"][-1]
        self.assertEqual(private["image_sizes"], ["7", "8"])
        self.assertEqual(private["true_ratio_denominator"], "112")
        self.assertEqual(private["true_convergent_index"], 2)
        self.assertEqual((private["setup_fraction"], private["after_setup_fraction"]), ("1/2", "3/7"))
        for case in actual:
            for row in case["rows"]:
                count = int(row["hits_after_setup"])
                if case["control"] == "crossed" or row["choice"].startswith("lcm-through"):
                    self.assertEqual(count, 0)
                if row["choice"] != "chosen-with-known-factors":
                    self.assertLess(Fraction(row["setup_fraction"]), Fraction(1, 2**415))
