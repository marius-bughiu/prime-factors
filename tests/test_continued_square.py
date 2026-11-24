from math import gcd
import unittest

from experiments.continued_square import search


class ContinuedSquareTests(unittest.TestCase):
    def test_every_promised_small_family_pair_is_recovered(self):
        # Adjust the parameter just beyond the strict Legendre threshold.
        for a in range(1, 9):
            for b in range(a + 1, 2*a + 1):
                if gcd(a, b) != 1:
                    continue
                d = b-a
                for g in (1, 3, 10):
                    i, j = g*a, g*b
                    t = 2 + (2*(i+1)*(j+1)*d**2)//g**2
                    p, q = i*i*t+2*i+1, j*j*t+2*j+1
                    result = search(p*q)
                    self.assertEqual((result['factor'], result['cofactor']), (p, q))
                    self.assertEqual((result['a'], result['b'], result['scale']), (a, b, g))

    def test_no_convergents(self):
        self.assertEqual(search(49)['convergents'], 0)
        self.assertIsNone(search(143, 0)['factor'])
