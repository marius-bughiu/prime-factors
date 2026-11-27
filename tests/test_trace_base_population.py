import json
import unittest
from collections import Counter
from math import gcd

from experiments.mixed_ratio_heights import jacobi
from experiments.trace_base_population import CATEGORIES, RECORD, report, tally
from experiments.weighted_global_trace import schedule, trace_search


class TraceBasePopulationTests(unittest.TestCase):
    def test_every_base_against_public_search(self):
        for p, q in ((17, 23), (29, 31), (37, 53)):
            n = p*q
            h = n//2
            gaps, coords, _ = schedule(n, p.bit_length(), 64, 2)
            totals = {"positive": Counter(), "negative": Counter()}
            for base in range(1, n):
                if gcd(base, n) != 1:
                    continue
                out = totals["positive" if jacobi(base, n) == 1 else "negative"]
                out["units"] += 1
                full = trace_search(n, base, gaps, coords, True)[0]
                off = full["first_off_gap_factor"] is not None
                out["off_including_setup_bases"] += off
                if full["setup_divisors"]:
                    out["setup"] += 1
                    continue
                has_hit = bool(full["divisors"])
                own = bool(trace_search(n, base, gaps, coords, False)[0]["divisors"])
                out["off_after_setup"] += off
                out["own_after_setup"] += own
                out["extra_after_own"] += has_hit and not own
                out["all_after_setup"] += has_hit
                has_local = any(1 < gcd(pow(base, s-(h+1)*c, n) - pow(base, sign*h*d, n), n) < n
                                for _, _, c, s, _ in coords for d in gaps for sign in (-1, 1))
                out["local_after_setup"] += has_local
            expected = {sign: {k: str(t[k]) for k in CATEGORIES} for sign, t in totals.items()}
            self.assertEqual(tally(p, q, p.bit_length(), 64, 2)["totals"], expected)

    def test_reproduce_large_controls(self):
        rows = report()
        self.assertEqual(rows, json.loads(RECORD.read_text()))
        self.assertEqual(len(rows), 2)
        for row, power, count in zip(rows, (1021, 717), (48, 0)):
            def total(key):
                return sum(int(group[key]) for group in row["totals"].values())
            self.assertGreater(total("units"), 2**2047)
            self.assertGreater(total("units"), total("setup") * 2**power)
            self.assertEqual(total("all_after_setup"), count)
            self.assertEqual(total("off_after_setup"), 0)
