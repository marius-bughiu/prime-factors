import unittest
from collections import Counter
from math import gcd, isqrt

from experiments.local_midpoint_lanes import count_intersection, midpoint_lanes, search


class LocalMidpointLanesTests(unittest.TestCase):
    def test_disjoint_lanes_match_factor_pairs(self):
        for p, top in ((2, 7), (3, 4), (5, 3), (7, 2)):
            for e in range(1, top+1):
                period = p**e
                for n in range(1, min(period, 24)+1):
                    if gcd(n, p) != 1:
                        continue
                    sums = {(x+n*pow(x, -1, period)) % period
                            for x in range(period) if gcd(x, p) == 1}
                    expected = {h for h in range(period) if 2*h % period in sums}
                    lanes = midpoint_lanes(n, p, e)
                    siblings = Counter((b.modulus, b.residue % (b.modulus//p))
                                       for b in lanes if b.modulus > 1)
                    self.assertTrue(all(count < p for count in siblings.values()))
                    actual = [h for lane in lanes for h in range(lane.residue, period, lane.modulus)]
                    self.assertEqual(sorted(actual), sorted(expected), (p, e, n))

    def test_all_powers_and_arbitrary_interval_endpoints(self):
        n = 34387
        primes = [2, 3, 5]
        report = search(n, primes)
        groups = [midpoint_lanes(n, p, e) for p, e, _ in report['prime_exponent_classes']]
        expected = [194]
        for lo in range(report['low'], report['high']+1):
            for hi in range(lo-1, report['high']+1):
                self.assertEqual(count_intersection(lo, hi, groups), sum(lo <= x <= hi for x in expected))
        self.assertEqual((report['survivors'], report['midpoint'], report['factor']), (1, 194, 137))
        d = isqrt(194*194-n)
        self.assertEqual((194-d, 194+d), (137, 251))

    def test_auxiliary_divisor_and_invalid_input(self):
        self.assertEqual(search(35, [2, 5])["factor"], 5)
        for primes in ([1], [2, 2], [9]):
            with self.assertRaises(ValueError):
                search(35, primes)

    def test_saturation_includes_false_midpoints(self):
        n, primes = 1000003*1900009, [2, 3, 5]
        report = search(n, primes)
        stronger = [midpoint_lanes(n, p, e+3) for p, e, _ in report['prime_exponent_classes']]
        self.assertEqual(report['survivors'], count_intersection(report['low'], report['high'], stronger))
        self.assertGreater(report['survivors'], 1)
