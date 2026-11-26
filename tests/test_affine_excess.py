from itertools import combinations
from math import gcd, isqrt
import unittest

from experiments.affine_excess import compare, normalized_rows
from experiments.weighted_square_pairs import first_label


class AffineExcessTests(unittest.TestCase):
    def test_normalized_rows_match_every_direct_ceiling(self):
        for n in (5, 77, 10961, (1 << 127)-1):
            normalized, fallbacks = normalized_rows(n, 8, 2)
            direct = set()
            for a in range(1, 9):
                for b in range(1, 9):
                    start, stride = first_label(n, a*a*n+b)
                    for label in (start, start+stride):
                        c = label-2*a*n
                        u = a*c-b
                        self.assertEqual(label*label-4*(a*a*n+b)*n, 4*u*n+c*c)
                        direct.add((u, c))
            self.assertEqual(set(normalized), direct)
            if n == 5:
                self.assertGreater(fallbacks, 0)

    def test_pruned_and_reconstructed_pairs_match_direct_square_tests(self):
        for n in (5, 77, 10961):
            rows, _ = normalized_rows(n, 8, 2)
            square_count = minus = plus = either = 0
            for (u, c), (v, d) in combinations(rows, 2):
                product = (4*u*n+c*c)*(4*v*n+d*d)
                z = isqrt(product)
                if z*z != product:
                    continue
                square_count += 1
                m, p = gcd(c*d-z, n), gcd(c*d+z, n)
                minus += 1 < m < n
                plus += 1 < p < n
                either += (1 < m < n or 1 < p < n)
            result = compare(n, 8, 2)
            work = result['work']
            self.assertEqual(work['pairs'], len(rows)*(len(rows)-1)//2)
            self.assertEqual(result['remaining_pairs'], 0)
            self.assertEqual(work['pair_gcds'], 2*square_count)
            self.assertEqual((work['proper_pair_minus'], work['proper_pair_plus'],
                              work['proper_pair_either']), (minus, plus, either))

    def test_actual_nonsingular_square_also_reached_by_baselines(self):
        hits = compare(10961, 8, 2)['hits']
        self.assertEqual(hits['two_nonsquares']['rows'], [[12, 5], [24, 26]])
        self.assertEqual(hits['two_nonsquares']['root'], '744314')
        self.assertEqual((hits['two_nonsquares']['minus'], hits['two_nonsquares']['plus']),
                         ('97', '113'))
        self.assertNotIn('affine_single', hits)
        self.assertTrue(all(arm in hits for arm in ('ordinary', 'raw', 'stride')))
