import json
import unittest
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path

from experiments.gap_coverage import primes_through
from experiments.mixed_ratio_heights import jacobi
from experiments.short_norm_boxes import coordinate_ranges, count_progression, plan, search


class ShortNormBoxTests(unittest.TestCase):
    def test_representations_for_every_odd_prime_through_2000(self):
        for prime in primes_through(2000)[1:]:
            side = isqrt(prime)
            residue = prime % 8
            d = -1 if residue in (1, 5) else -2 if residue == 3 else 2
            _, first, last, step = coordinate_ranges(prime, prime, side, [d], True)[0]
            target = -prime if d == 2 else prime
            self.assertTrue(any(u*u - d*v*v == target
                                for u in range(1, side+1, 2)
                                for v in range(first, last+1, step)), prime)

    def test_complete_scan_finds_a_proper_divisor_without_factor_labels(self):
        for p, q in combinations(primes_through(83)[1:], 2):
            for balanced in ((False, True) if q <= 2*p else (False,)):
                result = search(p*q, 100, balanced=balanced)
                self.assertIn(result["factor"], (p, q), (p, q, balanced))
                d, u, v, norm = result["witness"]
                self.assertEqual(int(u)**2-d*int(v)**2, int(norm))
                self.assertEqual(gcd(int(norm), p*q), result["factor"])

    def test_exact_success_count_for_short_separating_boxes(self):
        for p, q, h in ((11, 13, 2), (23, 31, 3), (37, 41, 4)):
            self.assertLess(2*h*h, p)
            n = p*q
            represented = {(u*u*pow(v*v, -1, p)) % p
                           for u in range(1,h+1) for v in range(1,h+1)}
            reduced = sum(gcd(u,v) == 1 for u in range(1,h+1) for v in range(1,h+1))
            self.assertEqual(len(represented), reduced)
            separating = [b for b in range(n) if jacobi(b,n) == -1]
            hits = sum(any(gcd(u*u-b*v*v,n) > 1 for u in range(1,h+1) for v in range(1,h+1))
                       for b in separating)
            self.assertEqual(hits*(p-1)*(q-1), len(separating)*reduced*(p+q-2))

    def test_registered_costs_and_factors(self):
        path = Path(__file__).resolve().parents[1] / "benchmarks" / "short-norm-boxes.json"
        for case in json.loads(path.read_text()):
            result = search(int(case["n"]), case["max_side"], balanced=case["balanced"])
            factor = result.pop("factor")
            self.assertEqual(result, {k: case[k] for k in result})
            if case["status"] == "complete":
                self.assertIn(str(factor), case["factors"])
            else:
                self.assertIsNone(factor)
                _, _, side, _, ranges = plan(int(case["n"]), 1<<520, balanced=True)
                queries = sum(count_progression(*row[1:]) for row in ranges)
                self.assertLess((side+1)//2 + queries, (4*side)*39//100)
