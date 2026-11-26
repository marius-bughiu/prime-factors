import unittest
from math import gcd

from experiments.cubic_readout_panel import compare
from experiments.cubic_square_readout import direct_readout, product, projected_readout
from experiments.cubic_trace_roots import decode
from experiments.cubic_trace_search import characteristic


class CubicReadoutTests(unittest.TestCase):
    def test_specialize_in_the_original_basis(self):
        f, m, n = (31, 0, 0), 6, 247
        beta = product(f, (14, 1, 0), (14, 1, 0))
        root, = decode(*characteristic(f, beta))['witnesses']
        direct = direct_readout(n, m, f, beta, 58, root)
        self.assertEqual(direct['denominator'], 1)
        self.assertEqual(sorted(direct['gcds']), [13, 19])
        proj = projected_readout(n, m, f, beta, 58)
        self.assertEqual(sorted(proj['gcds'][0]), [13, 19])
        with self.assertRaises(ValueError):
            direct_readout(n, m, f, beta, 58, dict(root, numerators=[1, 2, 3]))

    def test_real_row_dependency_missed_by_both_ordinary_gcds(self):
        case = compare(1333, cap=59)
        hit = case['first_rescue']
        self.assertEqual(hit['index'], 59)
        self.assertEqual(hit['ordinary'], [[1333, 1333]])
        self.assertEqual(hit['projected']['signed_traces'], [566316738])
        self.assertEqual(hit['projected']['gcds'], [[31, 43]])
        self.assertEqual(len(hit['rows']), 14)
        self.assertGreater(hit['direct'][0]['cancelled_content'], 1)

    def test_projected_congruence_at_a_repeated_prime(self):
        # f(3)=25. Construct integral field squares independently of the trace search.
        f, n, m = (-2, 0, 0), 25, 3
        for root in ((1, 0, 0), (0, 1, 0), (4, -2, 1), (2, 1, 0)):
            beta = product(f, root, root)
            z = sum(c*m**i for i, c in enumerate(root))
            result = projected_readout(n, m, f, beta, z)
            self.assertTrue(result['signed_traces'])
            self.assertTrue(all((u*u-(27*z)**2) % n == 0 for u in result['signed_traces']))
            self.assertEqual(result['derivative_gcd'], gcd(n, 27))
