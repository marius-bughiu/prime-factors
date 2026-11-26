import json
from math import isqrt
from pathlib import Path
import unittest

from experiments.affine_radix_holdout import draw_prime
from experiments.factor_sum_quantile import sum_bounds


class FactorSumQuantile(unittest.TestCase):
    def test_integer_cut_agrees_with_factor_criterion(self):
        for bits in range(2, 7):
            bound = 1 << bits
            for p in range(bound // 2, bound):
                for q in range(p, bound):
                    n = p*q
                    if n.bit_length() != 2*bits:
                        continue
                    low, center, high = sum_bounds(n, bits)
                    self.assertLessEqual(low, p+q)
                    self.assertLessEqual(p+q, high)
                    self.assertEqual(p+q <= center, q**3 <= bound**2*p)
                    def passes(s):
                        return bound**2 * (s*s-2*n)**2 <= n*(bound**2+n)**2
                    if center >= low:
                        self.assertTrue(passes(center))
                    if center < high:
                        self.assertFalse(passes(center+1))

    def test_unrounded_cut_and_promise(self):
        # For the public upper bound (B²+n)/B, the maximum integer strictly
        # below it must be used, even when the division is exact.
        n = 12*13
        low, center, high = sum_bounds(n, 4)
        self.assertEqual(low, isqrt(4*n-1)+1)
        self.assertEqual(high, (256+n-1)//16)
        self.assertLessEqual(center, high)
        self.assertEqual(sum_bounds(12*12, 4)[2], 24)
        with self.assertRaises(ValueError):
            sum_bounds(17, 4)
        with self.assertRaises(ValueError):
            sum_bounds(-197, 4)

    def test_holdouts_use_first_eight_eligible_draws(self):
        path = Path(__file__).resolve().parents[1] / 'benchmarks' / 'factor-sum-quantile.json'
        cases = [c for c in json.loads(path.read_text()) if 'sample' in c]
        actual = []
        for sample in range(cases[-1]['sample']+1):
            p, q = sorted(draw_prime(side, sample, bits=40, seed=b'factor-sum-quantile-v1')
                          for side in (b'p', b'q'))
            if p != q and (p*q).bit_length() == 80:
                actual.append((sample, str(p*q), [str(p), str(q)]))
        self.assertEqual(len(actual), 8)
        self.assertEqual(actual, [(c['sample'], c['n'], c['factors']) for c in cases])
