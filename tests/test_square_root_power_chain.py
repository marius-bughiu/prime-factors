from math import gcd, isqrt
import unittest

from experiments.square_root_power_chain import parameters, search


class SquareRootPowerChainTests(unittest.TestCase):
    def test_lone_gcd_detects_every_chain_with_a_proper_divisor(self):
        for n in range(3,2000,2):
            for mode in ('powers-of-two','product-minus-one'):
                initial,height = parameters(n,mode)
                values = [gcd(pow(isqrt(n),initial << j,n)-1,n) for j in range(height+1)]
                proper = {d for d in values if 1 < d < n}
                divisor, run = search(n,mode)
                self.assertEqual(divisor is not None,bool(proper))
                self.assertLessEqual(run['gcd_calls'],1)
                if divisor is not None:
                    self.assertIn(divisor,proper)
                if run['first_whole'] is not None:
                    self.assertEqual(values[run['first_whole']],n)
                if run['checked_index'] is not None:
                    self.assertEqual(int(run['checked_gcd']),values[run['checked_index']])

    def test_last_nonwhole_finds_a_factor_hidden_at_the_terminal_exponent(self):
        for n,mode,expected,whole in (
                (536033,'powers-of-two',929,6),
                (33227,'product-minus-one',149,1)):
            divisor, run = search(n,mode)
            self.assertEqual(divisor,expected)
            self.assertEqual(run['first_whole'],whole)
            self.assertEqual(run['checked_index'],whole-1)

    def test_chain_that_begins_at_one_requires_no_gcd(self):
        divisor, run = search(9,'product-minus-one')
        # This particular base is a nonunit; it never reaches one.
        self.assertIsNone(divisor)
        self.assertEqual(run['gcd_calls'],1)
        divisor, run = search(3,'powers-of-two')
        self.assertIsNone(divisor)
        self.assertEqual(run['first_whole'],0)
        self.assertEqual(run['gcd_calls'],0)
