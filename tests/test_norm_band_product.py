import json
import unittest
from itertools import combinations
from math import gcd, isqrt, prod
from pathlib import Path

from experiments.gap_coverage import primes_through
from experiments.norm_band_product import cover, search


def direct_values(side):
    """Enumerate the normalized forms directly, without bounds from the search."""
    for u in range(1, side + 1, 2):
        for v in range(1, side + 1):
            if v % 2:
                yield -2, v, u*u + 2*v*v
            else:
                yield -1, v, u*u + v*v
                yield 2, v, 2*v*v - u*u


class NormBandProductTests(unittest.TestCase):
    def test_dyadic_segments_partition_every_small_slice(self):
        for stop in range(35):
            for start in range(stop + 1):
                indices = []
                for level, index in cover(start, stop):
                    length = 1 << level
                    indices.extend(range(index*length, (index + 1)*length))
                self.assertEqual(sorted(indices), list(range(start, stop)))

    def test_clipping_agrees_with_direct_enumeration_at_each_cap(self):
        for n in (15, 77, 143, 323, 713, 2021, 1009*1201):
            for balanced in (False, True):
                lower = max(3, isqrt((n - 1)//2) + 1) if balanced else 3
                upper = isqrt(n)
                target = isqrt(upper)
                for cap in range(target + 2):
                    side = min(cap, target)
                    included = [(d, v, value) for d, v, value in direct_values(side)
                                if lower <= value <= upper]
                    expected = gcd(n, prod(value for _, _, value in included))
                    with self.subTest(n=n, balanced=balanced, cap=cap):
                        result = search(n, cap, balanced=balanced)
                        self.assertEqual(result['factor'], expected if expected > 1 else None)
                        self.assertEqual(result['allowed_pairs'], len(included))
                        self.assertEqual(result['denominators'], len({(d, v) for d, v, _ in included}))
                        self.assertEqual(result['gcds'], 1)

    def test_whole_modulus_becomes_the_smaller_prime(self):
        self.assertEqual(gcd(prod(value for _, _, value in direct_values(4)), 713), 713)
        self.assertEqual(search(713, 4)['factor'], 23)
        self.assertEqual(search(713, 5, balanced=True)['factor'], 23)

    def test_full_side_returns_exact_smaller_prime(self):
        for p, q in combinations(primes_through(101)[1:], 2):
            modes = (False, True) if q <= 2*p else (False,)
            for balanced in modes:
                with self.subTest(p=p, q=q, balanced=balanced):
                    result = search(p*q, isqrt(isqrt(p*q)), balanced=balanced)
                    self.assertEqual(result['factor'], p)
                    self.assertEqual(result['gcds'], 1)

    def test_benchmark_work_and_outcomes(self):
        path = Path(__file__).resolve().parents[1] / 'benchmarks' / 'norm-band-product.json'
        for case in json.loads(path.read_text()):
            with self.subTest(case=case['id']):
                result = search(int(case['n']), case['max_side'], balanced=case['balanced'],
                                canonical=case.get('canonical', False))
                factor = result.pop('factor')
                self.assertEqual(result, {k: case[k] for k in result})
                if case['status'] == 'complete':
                    self.assertEqual(str(factor), case['factors'][0])
                else:
                    self.assertIsNone(factor)
                    self.assertEqual(case['remaining'], [case['n']])
                    self.assertEqual(result['allowed_pairs'], 0)
                    self.assertEqual(result['evaluations'], 0)
