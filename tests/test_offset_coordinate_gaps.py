import unittest
from math import gcd, isqrt

from experiments.offset_coordinate_gaps import chart, exact_gaps, residues, search
from experiments.offset_winner_window import bounds


class CoordinateGapsTest(unittest.TestCase):
    def test_wrapped_residue_intervals(self):
        for modulus in range(1,12):
            for low in range(-14,10):
                for width in range(-1,15):
                    intervals = residues(low,low+width,modulus)
                    found = {i for a,b in intervals for i in range(a,b)}
                    self.assertEqual(found, {i % modulus for i in range(low,low+width+1)})

    def test_both_orientations_and_square_root_fallback(self):
        for modulus in (4,16,36):
            for z in range(25):
                for signed in {z,-z}:
                    for high in (z,z+4*modulus):
                        work = dict(gap_square_checks=0,fallback_roots=0)
                        got = exact_gaps(z*z,signed % modulus,modulus,(0,1,0,high),0,work)
                        self.assertEqual(got, sorted(r for r in {z,-z} if r % modulus == signed % modulus))
                        self.assertEqual(exact_gaps(z*z+2,signed % modulus,modulus,(0,1,0,high),0,work), [])

    def test_search_recovers_all_represented_positions(self):
        for p,q in ((17,23),(67,89),(101,103),(257,457)):
            n = p*q
            t = isqrt(n)
            box = bounds(n)
            expected = set()
            for v in range(1,isqrt(box['K'])+1):
                for s in range(1,box['K']//v+1):
                    j = p*s*s+q*v*v-2*t*s*v
                    if 0 < j <= box['J'] and gcd(s,v) == 1 and gcd(j,s*v) == 1:
                        expected.add((j,s*v,str(p),str(q)))
            self.assertTrue(expected)
            for parts in (1,3,16):
                for tilted in (False,True):
                    run = search(n,parts,max_vectors=1000,max_tests=10000,all_vectors=True,tilted=tilted)
                    self.assertEqual({tuple(row) for row in run['hits']}, expected)
                    self.assertTrue(run['schedule_exhausted'])
                    self.assertEqual(run['untested_intervals'], 0)
                    self.assertLessEqual(run['tested_positions'], run['candidate_upper'])

    def test_overlapping_signs_and_budgets(self):
        one = chart(391,bounds(391),1,1,1,max_tests=1)
        self.assertEqual((one['candidate_upper'],one['tested_positions'],one['untested_intervals']), (2,1,0))
        none = chart(391,bounds(391),1,1,1,max_tests=0)
        self.assertEqual((none['tested_positions'],none['untested_intervals']), (0,1))
        run = search(117449,8,max_vectors=1,max_tests=1,all_vectors=True)
        self.assertFalse(run['schedule_exhausted'])
        self.assertEqual(run['tested_positions'],1)
        sample = search(117449,8,max_vectors=4)
        self.assertFalse(sample['all_vectors'])
        self.assertEqual(sample['tested_positions'],0)
