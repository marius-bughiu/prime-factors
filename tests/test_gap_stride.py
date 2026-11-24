from math import isqrt
import unittest

from experiments.gap_stride import search


class GapStrideTests(unittest.TestCase):
    def test_matches_direct_square_classes_on_small_inputs(self):
        for n in range(7, 1000, 2):
            if n % 5 == 0:
                self.assertEqual(search(n, 2, 2)['factor'], 5)
                continue
            found = search(n, 2, 2)['factor']
            root = isqrt(n - 1) + 1
            hits = set()
            for modulus in (1, 25, 625):
                for h in range(root, min(root + 2*modulus, (n + 1)//2)):
                    delta = h*h - n
                    if delta % modulus == 0 and isqrt(delta)**2 == delta:
                        hits.add(h - isqrt(delta))
            self.assertTrue(found in hits if hits else found is None, n)

    def test_empty_search(self):
        self.assertIsNone(search(77, 100, 0)['factor'])
        self.assertIsNone(search(5, 30, 1)['factor'])
