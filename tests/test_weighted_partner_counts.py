import json
from math import isqrt
from pathlib import Path
from random import Random
import unittest

from experiments.two_interior_population import search
from experiments.weighted_partner_counts import (
    UNITS24, partner_interval, plans, population, preceding_distance, primes_through,
)


def interval_flags(p, q, minimum):
    flags = 0
    for a, b, d, flag in plans(p % 24, q % 24, minimum):
        left, right = partner_interval(p, a, b, d)
        if left <= q <= right:
            flags |= flag
    return flags


def check_flags(test, p, q, minimum):
    common, ordinary, six, joint = search(p*q)
    expected = sum(flag for flag, hit in zip((1, 2, 4, 8), (common, common|ordinary, six, joint)) if hit)
    test.assertEqual(interval_flags(p, q, minimum), expected, (p, q))


class WeightedPartnerCountsTests(unittest.TestCase):
    def test_complete_direct_census(self):
        path = Path(__file__).resolve().parents[1] / 'research' / 'two-interior-population.json'
        direct = json.loads(path.read_text())
        counts = population(16)
        self.assertEqual({k: counts[k] for k in direct}, direct)

    def test_equality_at_preceding_row_is_excluded(self):
        # For q=4 or 36 the preceding trace is exactly the integer minimum.
        self.assertEqual(partner_interval(16, 1, 1, 4), (5, 35))
        self.assertEqual(preceding_distance(1, 1, 8), 24)
        self.assertEqual(preceding_distance(0, 24, 33), 33*24)

    def test_alternative_orientation(self):
        p, q = 419, 421
        orientations = plans(p % 24, q % 24, p)
        self.assertIn((2, 3, 48, 4), orientations)
        left, right = partner_interval(p, 2, 3, 48)
        self.assertLessEqual(left, q)
        self.assertLessEqual(q, right)
        check_flags(self, p, q, p)

    def test_direct_products_near_boundaries_and_across_bin(self):
        rng = Random(20261127)
        for bits in (16, 20, 24, 26):
            unit = 1 << bits
            divisors = primes_through(isqrt(unit))

            def nearest(start, step, lo, hi):
                for q in range(start, hi+1 if step > 0 else lo-1, step):
                    if lo <= q <= hi and all(q % r for r in divisors if r*r <= q):
                        return q
                return None

            tested = set()
            for hundredths in (63, 65, 77):
                p = nearest(hundredths*unit//100, 1, unit//2, unit-1)
                lo = max(p+1, (9*unit*unit + 16*p-1)//(16*p))
                hi = min(unit-1, 5*unit*unit//(8*p))
                for _ in range(32):
                    q = nearest(rng.randint(lo, hi), 1, lo, hi)
                    if q:
                        tested.add((p, q))
                for residue in UNITS24:
                    for a, b, d, flag in plans(p % 24, residue, unit//2):
                        for edge in partner_interval(p, a, b, d):
                            if not lo <= edge <= hi:
                                continue
                            # Closest primes strictly inside and outside a boundary.
                            for sign in (-1, 1):
                                start = edge + sign*(1+(sign*(residue-edge)-1) % 24)
                                q = nearest(start, sign*24, lo, hi)
                                if q:
                                    tested.add((p, q))
            self.assertGreater(len(tested), 100)
            for p, q in tested:
                check_flags(self, p, q, unit//2)
