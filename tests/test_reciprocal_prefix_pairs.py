from math import gcd, isqrt
from pathlib import Path
import json
import unittest

from experiments.reciprocal_prefix_pairs import farey_brackets, measure, projections, sweep
from scripts.benchmark import agree
from scripts.reciprocal_prefix_benchmark import prefix_case


class ReciprocalPrefixPairsTest(unittest.TestCase):
    def test_all_endpoints_and_occupied_pairs(self):
        for n in (247, 437, 899, 40913):
            scale = 1 << ((n.bit_length() + 1) // 2)
            for depth in range(6):
                brackets = farey_brackets(depth)
                first, second = projections(n, scale, brackets)
                merged, visits = sweep(first, second)
                self.assertLessEqual(visits, max(0, len(first) + len(second) - 1))
                domain = range(max(scale // 2 + 1, n // scale + 1), isqrt(n) + 1)
                expected = {}
                for p in domain:
                    f, = [i for i, ((a, b), (c, d)) in enumerate(brackets)
                          if a*p <= scale*b and scale*d < c*p]
                    g, = [i for i, ((a, b), (c, d)) in enumerate(brackets)
                          if a*n <= scale*p*b and scale*p*d < c*n]
                    expected.setdefault((f, g), []).append(p)
                self.assertEqual(merged, [(min(xs), max(xs)) for xs in expected.values()])

    def test_rejected_locations_and_exact_hits(self):
        for n in (247, 437, 899, 40913):
            for modulus in (1, 2, 3, 5, 7, 24):
                if gcd(n, modulus) != 1:
                    continue
                result = measure(n, depth=5, modulus=modulus)
                scale = 1 << ((n.bit_length() + 1) // 2)
                expected = [x for x in range(max(scale // 2 + 1, n // scale + 1), isqrt(n) + 1)
                            if gcd(x, modulus) == 1]
                self.assertEqual(result['candidates'], len(expected))
                self.assertLessEqual(result['eliminated'], result['inspected_lanes'])
                for x in result['exact_singletons']:
                    self.assertIn(x, expected)
                    self.assertEqual(n % x, 0)

    def test_benchmark_fixture(self):
        fixture = Path(__file__).resolve().parents[1] / 'benchmarks' / 'reciprocal-prefix-pairs.json'
        for case in json.loads(fixture.read_text()):
            divisor = prefix_case(case, None, agree, lambda _case, _path, p, *_: p)
            if divisor is None:
                self.assertEqual(case['remaining'], [case['n']])
                self.assertEqual(case['factors'], [])
            else:
                self.assertEqual([str(divisor), str(int(case['n']) // divisor)], case['factors'])


if __name__ == '__main__':
    unittest.main()
