"""Independent enumeration and outward-rounded density regressions."""

import json
from math import gcd, isqrt
from pathlib import Path
import unittest

from experiments.complete_offset_density import primitive_pair_bounds
from scripts.factor import primes_through


class CompleteOffsetDensityTests(unittest.TestCase):
    def test_interval_contains_enumerated_share(self):
        t, h = 580_000, 1_000_003
        j_limit = isqrt(4*h//3)
        # -h is 1 modulo 4 and 5 modulo 8. The first obstruction at two is 8.
        self.assertEqual((-h) % 8, 5)
        total = kept = 0
        for j in range(1, j_limit+1):
            count = sum(gcd(j, k) == 1 for k in range(1, t*j//h+2))
            total += count
            if j % 8:
                kept += count
        bounds = primitive_pair_bounds(t*t+h, [2])
        self.assertLessEqual(bounds['minimum_percent_units']*total, kept*10**8)
        self.assertLessEqual(kept*10**8, bounds['maximum_percent_units']*total)
        self.assertLessEqual(bounds['surviving_pairs_at_least'], kept)

    def test_full_size_finite_bounds(self):
        fixtures = Path(__file__).resolve().parents[1]/'benchmarks/grouped-norm.json'
        expected = {'grouped-norm-fresh-2048': ((26410182, 26410183), 1020),
                    'grouped-norm-crossed-2048': ((21432102, 21432103), 1019)}
        primes = primes_through(10**6)
        checked = set()
        for case in json.loads(fixtures.read_text()):
            if case['id'] in expected:
                interval, exponent = expected[case['id']]
                result = primitive_pair_bounds(int(case['n']), primes)
                self.assertEqual((result['minimum_percent_units'], result['maximum_percent_units']), interval)
                self.assertGreater(result['surviving_pairs_at_least'], 2**exponent)
                checked.add(case['id'])
        self.assertEqual(checked, set(expected))
