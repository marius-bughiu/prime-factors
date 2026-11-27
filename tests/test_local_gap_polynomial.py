import json
import unittest
from time import process_time_ns

from experiments.local_gap_polynomial import (LOCAL, ROOT, Readouts, check_fixture, keys,
                                              local_search, run_fixture, run_method)
from experiments.weighted_global_trace import schedule


class LocalGapProducts(unittest.TestCase):
    def test_fixed_complete_and_partial(self):
        cases = json.loads((ROOT/"benchmarks/local-gap-polynomial.json").read_text())
        for case in cases:
            with self.subTest(case=case["id"]):
                inputs = {k:case[k] for k in ("n","factor_bits","multiplier_limit","per_row")}
                check_fixture(case, run_fixture(inputs))

    def test_global_equality_and_two_single_prime_matches(self):
        # At Y=1 the exact match forces P(1)=0. After its removal the
        # differences from 8 and 12 still supply one hit at each prime.
        for method in LOCAL:
            with self.subTest(method=method):
                out = Readouts(77, process_time_ns())
                local_search(method, 77, [1, 8, 12], {0: 1}, 1, out)
                self.assertEqual(out.divisors, {7, 11})
                if method == "derivative":
                    self.assertEqual(out.work["derivative_queries"], 1)
                    self.assertGreater(out.work["bisect_proper"], 0)

    def test_shared_exact_root_alone_yields_no_factor(self):
        for method in LOCAL:
            out = Readouts(77, process_time_ns())
            local_search(method, 77, [1], {0: 1}, 1, out)
            self.assertEqual(out.divisors, set())
            if method == "derivative":
                self.assertEqual(out.work["column_one"], 1)
                self.assertEqual(out.work["replay_whole"], 0)

    def test_keys_and_first_blind_gain(self):
        n, h = 1433779, 1433779 // 2
        gaps, coords, _ = schedule(n, 11, 256, 4)
        _, left, signed = keys(n, gaps, coords, Readouts(n, process_time_ns()))
        self.assertEqual(left, [pow(2, s-(h+1)*c, n) for _, _, c, s, _ in coords])
        self.assertEqual(signed, {e: pow(2, h*e, n) for e in signed})
        for method in ("global", "square", *LOCAL):
            found = run_method(method, n, 11, 256, 4)[0]["divisors"]
            self.assertEqual(found, [1097] if method in LOCAL else [])

    def test_overlapping_gap_values(self):
        # A low-order base can repeat both signed right values and left keys.
        for n, v in ((35, 4), (77, 2), (143, 3)):
            signed = {e: pow(v, e, n) for e in range(-14, 15)}
            left = list(dict.fromkeys([1, 3, 4, 8, 11, 22, *signed.values()]))
            found = []
            for method in LOCAL:
                out = Readouts(n, process_time_ns())
                local_search(method, n, left, signed, v, out)
                found.append(out.divisors)
            self.assertTrue(all(g == found[0] for g in found))
