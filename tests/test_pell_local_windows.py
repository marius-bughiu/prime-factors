import unittest
from math import gcd, isqrt

from experiments.pell_local_windows import search


class LocalWindowTest(unittest.TestCase):
    def test_full_convergents_independently_recover_first_witnesses(self):
        # The reference can afford unbounded convergent coordinates on these inputs.
        for n in (77, 221, 1517, 34387, 21490481):
            root = isqrt(n)
            quotient, p, q = root, 0, 1
            old_x, x, old_y, y = 0, 1, 1, 0
            history = []
            expected = {'ordinary_pair': None, 'shifted_pair': None}
            for j in range(1, 121):
                old_x, x = x, quotient*x + old_x
                old_y, y = y, quotient*y + old_y
                p = quotient*q - p
                q = (n-p*p)//q
                quotient = (root+p)//q
                for i, xx, yy in reversed(history[-8:]):
                    w, v = abs(x*xx - n*y*yy), abs(x*yy - xx*y)
                    if (root+1)*(v+4) >= n:
                        continue
                    r = w*w - n*v*v
                    for radicand in range(r % n, 4*n, n):
                        z = isqrt(radicand)
                        if z == w or z*z != radicand:
                            continue
                        k = (radicand-r)//n
                        kind = 'shifted_pair' if k else 'ordinary_pair'
                        if expected[kind] is None:
                            expected[kind] = dict(i=i, j=j, v=v, w=w, z=z, k=k,
                                                  signed_product=r, factor=gcd(w+z, n))
                history.append((j, x, y))
                if q == 1:
                    break
            result = search(n, 120, 8)
            self.assertEqual({key: result[key] for key in expected}, expected)

    def test_empty_budget_and_period_end(self):
        self.assertEqual(search(34387, 0)['pairs'], 0)
        self.assertEqual(search(34387, 16, 0)['pairs'], 0)
        self.assertEqual(search(2*5, 100)['steps'], 1)
        with self.assertRaises(ValueError):
            search(121)
