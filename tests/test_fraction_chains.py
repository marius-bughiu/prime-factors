from collections import defaultdict
from math import gcd
import unittest

from experiments.fraction_chains import euclidean_pairs, search


class FractionChainTests(unittest.TestCase):
    def test_every_reduced_signed_fraction_with_small_product_is_enumerated(self):
        for n in range(3, 128):
            by_residue = defaultdict(set)
            for a in range(1, (n-1)//2+1):
                if gcd(a,n) != 1:
                    continue
                inverse = pow(a,-1,n)
                for b in range(1,(n-1)//(2*a)+1):
                    if gcd(a,b) != 1 or gcd(b,n) != 1:
                        continue
                    for signed in (-b,b):
                        by_residue[signed*inverse % n].add((signed,a))
            for residue in range(1,n):
                if gcd(n,residue) == 1:
                    observed = [(b,a) for _,b,a in euclidean_pairs(n,residue)
                                if 2*abs(a*b)<n and gcd(abs(b),a)==1]
                    self.assertEqual(len(observed),len(set(observed)))
                    self.assertEqual(set(observed),by_residue[residue])

    def test_two_fractions_from_one_draw_give_the_same_factor_for_each_root(self):
        n = 437
        roots = [x for x in range(n) if x*x % n == 104]
        self.assertEqual(len(roots),4)
        for x in roots:
            sample = lambda _n,_i: (x,1)
            first = search(n,'first',1,7,root_at=sample)
            all_rows = search(n,'all',1,7,root_at=sample)
            self.assertIsNone(first['factor'])
            self.assertEqual(all_rows['factor'],23)
            self.assertEqual(all_rows['smooth_rows'],2)
            self.assertEqual(all_rows['accepted_draws'],1)
            self.assertEqual(all_rows['selected_steps'],[[1,1],[1,3]])
            early = search(n,'all',1,7,online=True,root_at=sample)
            self.assertEqual(early['factor'],all_rows['factor'])

    def test_capped_and_nonunit_draws(self):
        for mode in ('first','all'):
            self.assertEqual(search(143,mode,0,13)['draws'],0)
            early = search(143,mode,2,13,root_at=lambda _n,_i:(11,1))
            self.assertEqual((early['factor'],early['outcome'],early['draws']), (11,'sample_gcd',1))
