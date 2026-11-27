import unittest
from collections import Counter
from itertools import product
from math import gcd
from random import Random

from experiments.complementary_keys import fold, search, shared_fold, target
from experiments.twelve_residue_collision import keys, mask, search as original


class ComplementaryKeyTests(unittest.TestCase):
    def test_all_local_fibers_and_middle(self):
        for p in (907, 1009, 1013, 1019):
            samples = [x for x in range(p) if mask(x, p)]
            old = Counter(keys(samples, p))
            counts = Counter(fold(u,p) for u in keys(samples,p))
            square = pow(3,(p-1)//2,p) == 1
            for u, count in old.items():
                opposite = (1-u) % p
                self.assertEqual(count,12)
                self.assertEqual(opposite in old,square)
                self.assertEqual(counts[fold(u,p)],24 if square and u != opposite else 12)

    def test_directed_product_against_each_pair(self):
        p, q = 1009, 1013
        n = p*q
        for seed in range(64):
            rng = Random(seed)
            samples = [rng.randrange(n) for _ in range(9)]
            samples = [x for x in samples if gcd(mask(x,n),n) == 1]
            values = keys(samples,n)
            work = {}
            found = target(samples,values,n,work)
            possible = [gcd(u+v-1,n) for u,v in product(values,repeat=2)]
            self.assertTrue(set(possible) <= {1,p})
            self.assertEqual(found, p if p in possible else None)
            if samples:
                self.assertEqual(work['target_gcds'],1)

    def test_shared_fold_refines_different_original_labels(self):
        p, q = 1009, 1013
        n = p*q
        ps = [x for x in range(p) if mask(x,p)]
        pv = keys(ps,p)
        x = 2
        u = keys([x],p)[0]
        y0 = ps[pv.index((1-u) % p)]
        y = y0 + p*((x-y0)*pow(p,-1,q) % q)
        a, b = keys([x,y],n)
        self.assertNotEqual(a,b)
        self.assertEqual(fold(a,n),fold(b,n))
        work = {'shared_gcds': 0}
        self.assertIn(shared_fold([x,y],[a,b],[fold(a,n),fold(b,n)],n,work),(p,q))
        self.assertEqual(work['source'],'shared fold')

    def test_euclidean_search_preserves_directed_hits(self):
        for p, q in ((1009,1013),(1019,1013),(1031,907)):
            n = p*q
            for draws in (0,1,2,7,16):
                for seed in range(24):
                    old = search(n,draws,seed,'target')[0]
                    new = search(n,draws,seed,'euclid')[0]
                    self.assertIn(new,(None,p,q))
                    if old:
                        self.assertIsNotNone(new)

    def test_retains_old_hits_and_finds_new_ones(self):
        for n in (1009*1013, 1009*1151, 1013*1019):
            for seed in (0,1,2,5,10,23,1044):
                before = original(n,8,seed,'twelve')[0]
                after = search(n,8,seed)[0]
                if before:
                    self.assertIsNotNone(after)
                if after:
                    self.assertEqual(n % after,0)
        for draws, seed, source in ((8,5,'pair'),(1,10,'middle')):
            n = 1009*1013
            self.assertIsNone(original(n,draws,seed,'twelve')[0])
            factor, work, _ = search(n,draws,seed)
            self.assertEqual(factor,1009)
            self.assertEqual(work['source'],source)
            self.assertEqual(search(n,draws,seed,'target')[0],1009)
        self.assertIsNone(search(1009*1013,0,0,'target')[0])
        with self.assertRaises(ValueError):
            search(1009*1019,5,0,'target')
