import unittest
from math import gcd, isqrt

from experiments.carry_interval import search
from experiments.radix_carries import nearest


def direct_hits(n, exponent, high, limit):
    radix = 1 << exponent
    coefficient = nearest(n, radix * radix) + high
    hits = set()
    for low in range(-limit, limit + 1):
        trace = coefficient * radix + nearest(n, radix) - low
        delta = trace * trace - 4 * coefficient * n
        if coefficient <= 0 or trace <= 0 or delta < 0:
            continue
        root = isqrt(delta)
        if root * root == delta and (trace + root) % 2 == 0:
            factor = gcd(n, (trace + root) // 2)
            if 1 < factor < n:
                hits.add((factor, low))
    return hits


class CarryIntervalTests(unittest.TestCase):
    def test_covered_intervals_match_every_direct_probe(self):
        statuses = set()
        for n in range(2, 155):
            for exponent in range(4):
                for high in (-1, 0, 1):
                    for limit in (0, 4, 16):
                        run = search(n, exponent, high, limit)
                        statuses.add(run['status'])
                        hits = {(int(h['factor']), int(h['low'])) for h in run['hits']}
                        if run['covered']:
                            self.assertEqual(hits, direct_hits(n, exponent, high, limit),
                                             (n, exponent, high, limit))
                            self.assertLessEqual(run['work']['trace_labels'], 2)
                            self.assertLessEqual(run['work']['root_candidates'], 4)
                        else:
                            self.assertEqual(run['status'], 'curvature_limit')
                            self.assertFalse(hits)
        self.assertEqual(statuses, {'empty', 'singleton', 'two_labels', 'curvature_limit'})
