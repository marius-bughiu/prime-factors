import unittest
from math import gcd, prod

from experiments.pell_pairs import center, search


class PellPairSearchTest(unittest.TestCase):
    def test_trivial_cycle_even_with_three_positive_norms(self):
        n = 2173
        roots = []
        for multiplier in (7*11, 7*47, 11*47):
            _, (denominator, sign, root) = center(n, multiplier, 300)
            self.assertEqual((denominator, sign), (multiplier, 1))
            self.assertEqual(gcd(denominator, n), 1)
            self.assertEqual(root*root % n, multiplier)
            roots.append(root)
        self.assertEqual(prod(roots) * pow(7*11*47, -1, n) % n, 1)

    def test_cycles_charge_the_shared_budget(self):
        cut = search(77837, 23, 825)
        self.assertIsNone(cut['factor'])
        self.assertEqual((cut['outcome'], cut['steps'], cut['centers']), ('budget', 825, 2))
        done = search(77837, 23, 826)
        self.assertEqual(done['root'], 39058)
        self.assertEqual(done['factor'], 277)
        self.assertEqual(done['cycles'], 1)

    def test_unmultiplied_center_for_two_primes_three_mod_four(self):
        for n in (7*11, 11*19, 31*43):
            _, (denominator, _, _) = center(n, 1, 300)
            self.assertGreater(gcd(n, denominator), 1)
            self.assertLess(gcd(n, denominator), n)
