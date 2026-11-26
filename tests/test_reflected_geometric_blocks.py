from math import gcd
import unittest

from experiments.geometric_lifted_readout import search
from experiments.reflected_geometric_blocks import reflected_polynomial
from experiments.weighted_stride_search import root_polynomial


class ReflectedGeometricBlocksTests(unittest.TestCase):
    def test_monic_coefficients_over_cubes(self):
        for n in (9, 11, 15, 25, 35, 77):
            modulus = n**3
            for ratio in range(1, n):
                if gcd(ratio, n) != 1:
                    continue
                for width in range(13):
                    roots = [pow(ratio, i, modulus) for i in range(width)]
                    work = {}
                    poly, factor = reflected_polynomial(roots, ratio, modulus, n, work)
                    if poly is not None:
                        self.assertEqual(poly, root_polynomial(roots, modulus))
                        self.assertIsNone(factor)
                    elif factor is None:
                        self.assertEqual(work['reflected_status'], 'tree_fallback')
                        self.assertTrue(any(gcd(1-r, n) == n for r in roots[1:width//2+1]))
                    else:
                        self.assertTrue(1 < factor < n and n % factor == 0)

    def test_batch_with_two_distinct_local_periods(self):
        n, ratio, width = 35, 9, 6
        work = {}
        roots = [pow(ratio, i, n**3) for i in range(width)]
        poly, factor = reflected_polynomial(roots, ratio, n**3, n, work)
        self.assertIsNone(poly)
        self.assertEqual(factor, 5)
        self.assertEqual(work['reflected_scan_gcds'], 2)
        self.assertEqual(work['reflected_inversions'], 0)

    def test_search_split_fallback_and_width_limit(self):
        n = 33127
        split = search(n, 158, 128, reflected=True)
        self.assertEqual((split['outcome'], split['factor']), ('reflected_denominator_gcd', 157))
        self.assertEqual(split['work']['unvisited_terms'], int(split['total_terms']))
        self.assertEqual(split['samples'], {})
        self.assertEqual(split['block_work']['root_polynomials'], 0)

        for ratio, status in ((2, 'coefficients'), (n-1, 'tree_fallback')):
            run = search(n, ratio, 128, reflected=True)
            ordinary = search(n, ratio, 128)
            self.assertEqual(run['block_work']['reflected_status'], status)
            for key in ('outcome', 'factor', 'samples', 'linear', 'quadratic'):
                self.assertEqual(run[key], ordinary[key])
        capped = search(n, 2, 1, reflected=True)
        self.assertEqual(capped['outcome'], 'block_width_limit')
        self.assertNotIn('block_work', capped)
