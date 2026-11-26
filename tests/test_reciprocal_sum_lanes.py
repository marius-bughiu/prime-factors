import unittest
from math import gcd, prod

from experiments.reciprocal_sum_lanes import METHODS, fermat, progression, search
from experiments.reciprocal_wheel import band


def direct(n, wheel, width, cap, tail):
    """Enumerate the actual feasible sums for each lower residue on small cases."""
    low, high = band(n)
    blocks = list(range(low, high+1, width))
    blocks = blocks[-cap:] if tail and cap else blocks[:cap]
    kept = []
    for start in blocks:
        end = min(high, start+width-1)
        for r in range(wheel):
            if gcd(r, wheel) != 1:
                continue
            lower = list(progression(start, end, wheel, r))
            if not lower:
                continue
            a, b = lower[0], lower[-1]
            s = n*pow(r, -1, wheel) % wheel
            if any(z % wheel == (r+s) % wheel
                   for z in range(b+(n+b-1)//b, a+n//a+1)):
                kept.extend(lower)
    return sorted(kept)


class ReciprocalSumLanesTest(unittest.TestCase):
    def test_old_control_and_matched_baselines(self):
        n = 15049
        reports = {m: search(n, 30, 120, 2, method=m) for m in METHODS}
        self.assertEqual(direct(n, 30, 120, 2, False), [89, 101, 119])
        self.assertEqual(reports['sum']['work']['ordinary_lower_terms'], 10)
        self.assertEqual(reports['tight_rectangle']['work']['product_terms'], 4)
        self.assertEqual(reports['sum']['work']['product_terms'], 3)
        self.assertEqual(reports['sum']['factor'], 101)
        self.assertEqual(reports['guarded_sum']['product'], reports['sum']['product'])

    def test_symbolic_lane_matches_explicit_sum_enumeration(self):
        for n in (77, 143, 323, 15049, 50629, 117449, 337):
            for width in (3, 11, 30, 120):
                for tail in (False, True):
                    for cap in (0, 2, 999):
                        with self.subTest(n=n, width=width, tail=tail, cap=cap):
                            expected = direct(n, 6, width, cap, tail)
                            for name in ('sum', 'guarded_sum'):
                                out = search(n, 6, width, cap, from_end=tail, method=name)
                                self.assertEqual(out['product'], str(prod(expected) % n))
                                self.assertEqual(out['work']['product_terms'], len(expected))
                                self.assertEqual(out['gcd'], str(gcd(prod(expected), n)))

    def test_guard_skips_pricings_and_fermat_respects_prefix(self):
        ordinary = search(1900014700027, 210, 840, 3)
        guarded = search(1900014700027, 210, 840, 3, method='guarded_sum')
        self.assertEqual(guarded['product'], ordinary['product'])
        self.assertEqual(guarded['work']['guarded_blocks'], 3)
        self.assertEqual(guarded['work']['lane_pricings'], 0)
        self.assertIsNone(fermat(15049, 30, 3, 0)['factor'])
        self.assertIsNone(fermat(15049, 30, 3, 1)['factor'])
        self.assertEqual(fermat(15049, 30, 3, 999)['factor'], 101)


if __name__ == '__main__':
    unittest.main()
