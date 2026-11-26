from itertools import combinations, product
from math import gcd, isqrt
import unittest

from experiments.gap_coverage import primes_through
from experiments.mixed_negative_norms import census, full_counts, search, squarefree_kernels, witness_lean


def direct_matches(n, weight, width=None):
    high = isqrt(weight*n-1)
    low = 1 if width is None else max(1, high-width+1)
    return [(t, weight*n-t*t) for t in range(low, high+1) if gcd(t, n) == 1]


def direct_counts(n, pairs):
    matches = splits = unequal = unequal_splits = 0
    for (t, d), (s, e) in pairs:
        z = isqrt(d*e)
        if z*z == d*e:
            matches += 1
            proper = 1 < gcd(t*s-z, n) < n
            splits += int(proper)
            if d != e:
                unequal += 1
                unequal_splits += int(proper)
    return matches, splits, unequal, unequal_splits


class MixedNegativeNormsTests(unittest.TestCase):
    def test_integer_join_against_pairwise_isqrt(self):
        primes = [p for p in primes_through(63) if p >= 32]
        kernels = squarefree_kernels(2*63**2)
        for p, q in combinations(primes, 2):
            n = p*q
            if n < 2048:
                continue
            with self.subTest(n=n):
                first, second = (direct_matches(n, w) for w in (1, 2))
                mixed = direct_counts(n, product(first, second))
                single = direct_counts(n, combinations(first, 2))
                counted, _ = full_counts(n, kernels)
                self.assertEqual(mixed, tuple(counted[k] for k in ('mixed_matches', 'mixed_splits',
                                 'mixed_unequal_matches', 'mixed_unequal_splits')))
                self.assertEqual(single[:2], (counted['single_matches'], counted['single_splits']))
                self.assertEqual(counted['mixed_equal_splits'], 1)

    def test_window_work_branches_and_small_boundaries(self):
        for n in (77, 2173, 2183, 43423):
            for width in (0, 1, 5, 32):
                with self.subTest(n=n, width=width):
                    result = search(n, width)
                    work = result['work']
                    first, second = (direct_matches(n, w, width) for w in (1, 2))
                    self.assertEqual(work['square_tests'], len(first)*len(second))
                    self.assertEqual(work['unit_labels'], [len(first), len(second)])
                    self.assertEqual(work['label_gcds'], sum(min(width, isqrt(w*n-1)) for w in (1, 2)))
                    self.assertEqual(direct_counts(n, product(first, second)), tuple(
                        work[k] for k in ('matches', 'splits', 'unequal_matches', 'unequal_splits')))
                    self.assertEqual(work['match_result_gcds'], 2*work['matches'])
                    self.assertEqual(work['representation_roots'], 2*work['matches'])
                    if result['factor']:
                        self.assertGreater(result['factor'], 1)
                        self.assertLess(result['factor'], n)
                        self.assertEqual(n % result['factor'], 0)
        for n, w in [(1, 32), (10, 1), (77, -1)]:
            with self.assertRaises(ValueError):
                search(n, w)

    def test_unequal_example_and_visible_direct_factor(self):
        result = search(43423)
        self.assertIsNone(result['direct_hit'])
        self.assertEqual((result['factor'], result['factor_source']), (251, 'mixed_match'))
        self.assertEqual(result['work']['square_tests'], 1024)
        w = result['unequal_witness']
        self.assertEqual([w[k] for k in ('t','s','d','e','g','root','gcd_minus','gcd_plus')],
                         ['193','264','6174','17150','686','10290','251','173'])
        self.assertIn('split_two_seven', witness_lean(43423,w))
        direct = search(2623)
        self.assertEqual(direct['factor_source'], 'label_gcd')
        self.assertIsNotNone(direct['unequal_witness'])
        self.assertIsNone(search(43423, 0)['factor'])

    def test_exception_and_smallest_absent_match(self):
        data = census(6)
        self.assertEqual(data['examples']['no_unequal_match'], {'n': '2183'})
        w = data['examples']['unequal_trivial']
        self.assertEqual((w['n'],w['trivial_quotient']), ('2173', {'sign': 1, 'j': '-1', 'v': '1'}))
        seven = data['by_mod8']['7']
        self.assertEqual(seven['mixed_unequal_matches'], seven['mixed_unequal_splits'])
        self.assertEqual(sum(v['products'] for v in data['by_mod8'].values()), data['total']['products'])
