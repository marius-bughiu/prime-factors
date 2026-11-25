from math import gcd, isqrt
import unittest

from experiments.grouped_offset_sweep import sweep


def without_duplicate_removal(n):
    t = isqrt(n)
    h = n-t*t
    for j in range(1, 33):
        k = (j*t-1)//h if h else 0
        if not k:
            continue
        common = gcd(gcd(j, k), n)
        if 1 < common < n:
            return j, common
        d = j*j+4*k*(t*j-h*k)
        root = isqrt(d)
        if root*root == d:
            m = (root-j)//2
            for candidate in (k*t-m, k*t+m+j):
                factor = gcd(n, candidate)
                if 1 < factor < n:
                    return j, factor
    return None


class GroupedOffsetSweepTests(unittest.TestCase):
    def test_skipping_a_scaled_test_preserves_the_first_factor(self):
        for n in range(2, 600):
            with self.subTest(n=n):
                found, work = sweep(n)
                self.assertEqual(found, without_duplicate_removal(n))
                self.assertEqual(work['eligible'], work['duplicates'] + work['square_tests']
                                 + work['multiplier_gcd_hits'])

    def test_first_success_at_thirteen(self):
        n = 2376225323
        self.assertIsNone(sweep(n, 12)[0])
        self.assertEqual(sweep(n, 13)[0], (13, 36559))
