from itertools import combinations
from math import gcd
import unittest

from experiments.mixed_ratio_heights import jacobi
from experiments.quartic_trace import decode, search


class QuarticTraceTests(unittest.TestCase):
    def test_prime_selected_by_the_twist_and_literal_sums(self):
        for p, q in combinations([5, 13, 17, 29, 37, 41, 53, 61, 73], 2):
            n = p*q
            bits = q.bit_length()
            r = search(n, n//2, 16, bits)
            if r['outcome'] == 'selector_divisor':
                self.assertIn(r['factor'], (p, q))
                continue
            d = r['selector']
            self.assertIsNotNone(d)
            selected = p if jacobi(d, p) == -1 else q
            traces = [sum(jacobi(x*(x*x-c), n) for x in range(n)) for c in (1, d)]
            self.assertEqual(gcd(n, sum(t*t for t in traces)), selected)
            self.assertEqual(r['residues'], [t % (4 << bits) for t in traces])
            self.assertEqual(r['factor'], selected)

    def test_prefix_never_enters_decoder_and_complete_inert_case(self):
        self.assertEqual(search(221, 109, 3)['residues'], None)
        self.assertIsNone(search(221, 109, 3)['factor'])
        self.assertEqual(search(77, 38, 3)['residues'], [0, 0])
        self.assertEqual(search(15, 7, 3)['outcome'], 'cancellation')
        self.assertEqual(search(65, 32, 2)['outcome'], 'selector_limit')

    def test_precision_control_and_signed_residues(self):
        n = 137*193
        self.assertIsNone(search(n, n//2, 3, 6)['factor'])
        self.assertEqual(search(n, n//2, 3, 8)['factor'], 137)
        self.assertEqual(decode(65, 4, 52, 24)[0], 5)
        self.assertEqual(decode(65, 4, -12, 24)[0], 5)
