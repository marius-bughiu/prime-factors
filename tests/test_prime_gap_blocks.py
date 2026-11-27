import unittest
from math import gcd, isqrt

from experiments.interior_prime_family import search, search_blocks, search_units


class PrimeGapBlockTests(unittest.TestCase):
    def test_block_alignment_and_rank(self):
        for n in range(5, 250, 2):
            if gcd(n, 6) != 1:
                continue
            first = isqrt(24*n-1)+1
            for blocks in (0, 1, 3):
                run = search_blocks(n, blocks)
                stop = first-first%6+6*blocks
                hits = []
                labels = [s for s in range(first,stop) if s%6 in (1,5)]
                for i, s in enumerate(labels, 1):
                    d = isqrt(s*s-24*n)
                    if d*d == s*s-24*n and 1 < gcd((s+d)//2,n) < n:
                        hits.append((s,i))
                self.assertEqual((run['trace'],run['tests']), hits[0] if hits else (None,len(labels)))

    def test_nonunit(self):
        with self.assertRaises(ValueError):
            search_blocks(21, 2)

    def test_equal_budget_preserves_every_split(self):
        for n in range(5, 1000, 2):
            if gcd(n, 6) != 1:
                continue
            for budget in (0, 1, 2, 5):
                old = search(n, budget)
                new = search_units(n, budget)
                self.assertLessEqual(new['tests'], budget)
                if old['factor'] is not None:
                    self.assertEqual(old['factor'],new['factor'])
                    self.assertLessEqual(new['tests'],old['tests'])
                if new['factor'] is None:
                    self.assertEqual(new['tests'], budget)
