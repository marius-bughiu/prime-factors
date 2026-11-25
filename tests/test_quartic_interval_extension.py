import unittest
from collections import Counter
from itertools import product
from math import gcd

from experiments.quartic_divisor_window import search
from experiments.quartic_interval_extension import _sign_runs, extend


def polynomial(coefficients, x):
    return sum(a*x**i for i,a in enumerate(coefficients))


class QuarticIntervalExtensionTests(unittest.TestCase):
    def test_sign_partition_matches_every_integer(self):
        # Include constants, zero polynomials, multiple roots and lower degrees.
        for coefficients in product((-1,0,1),repeat=5):
            for left,right in ((-8,9),(-1,-1),(2,1)):
                runs = _sign_runs(coefficients,left,right,Counter())
                result = [(x,sign) for a,b,sign in runs for x in range(a,b+1)]
                expected = []
                for x in range(left,right+1):
                    y = polynomial(coefficients,x)
                    expected.append((x,(y>0)-(y<0)))
                self.assertEqual(result,expected,coefficients)
                self.assertTrue(all(s!=t for (_,_,s),(_,_,t) in zip(runs,runs[1:])))

    def test_connected_component_and_neighbors_against_direct_search(self):
        checked = 0
        for n,c in ((41,5),(77,9),(107,13),(143,11),(323,17),(2501,43)):
            for stride in (1,2,3):
                if gcd(n,stride)!=1:
                    continue
                work = search(n,c,1,stride=stride)
                if not work['relation_verified']:
                    continue
                result = extend(work)
                good = {x for x in range(-c,n+1)
                        if 1<=c+stride*x<=n and
                        abs(polynomial(work['coefficients'],x)) < (c+stride*x)**2}
                self.assertIn(0,good)
                first = last = 0
                while first-1 in good:
                    first -= 1
                while last+1 in good:
                    last += 1
                self.assertEqual((result['first_offset'],result['last_offset']),(first,last))
                self.assertEqual(result['left_neighbor_fails'],c+stride*(first-1)>=1)
                self.assertEqual(result['right_neighbor_fails'],c+stride*(last+1)<=n)
                expected = [c+stride*x for x in range(first,last+1) if n%(c+stride*x)==0]
                self.assertEqual(result['divisors'],expected)
                if (n,c,stride)==(107,13,1):
                    self.assertIn(-4,good)
                    self.assertNotIn(-3,good)
                    self.assertEqual(first,-2)
                checked += 1
        self.assertGreaterEqual(checked,10)

    def test_two_bernstein_blocks_and_rechecked_modulus(self):
        result = extend(search(41,5,1,stride=1))
        self.assertEqual((result['first_offset'],result['last_offset']),(-1,3))
        self.assertEqual(result['cuts'],[1])
        self.assertEqual((result['certified_blocks'],result['bernstein_tests']),(2,3))
        self.assertTrue(result['left_neighbor_fails'] and result['right_neighbor_fails'])
        self.assertEqual(result['rootless_modulus'],2)
        self.assertEqual((result['rootless_residue_checks'],result['integer_root_nodes']),(2,0))
        self.assertEqual((result['jet_checks'],result['additional_lll_calls']),(2,0))
        self.assertTrue(result['excluded'])

    def test_degree_drop_equality_and_clipping(self):
        # F=(x−3)² vanishes doubly at the public anchor. The magnitude
        # comparison is an equality at d=39, x=−36 when the center is 75.
        work = dict(n=78,center=75,stride=1,radius=1,anchor=3,
                    coefficients=[9,-6,1,0,0],height=16,
                    relation_verified=True,rootless_modulus=None,modulus_limit=0)
        result = extend(work)
        self.assertEqual((result['lower'],result['upper'],result['divisors']),(40,78,[78]))
        self.assertTrue(result['left_neighbor_fails'])
        self.assertFalse(result['right_neighbor_fails'])
        clipped = extend(work,lower=74,upper=75)
        self.assertEqual((clipped['first_offset'],clipped['last_offset']),(-1,0))
        self.assertEqual((clipped['neighbor_tests'],clipped['divisors']),(0,[]))
        self.assertTrue(clipped['excluded'])
        singleton = extend(work,lower=75,upper=75)
        self.assertEqual((singleton['progression_size'],singleton['certified_blocks']),(1,1))

    def test_rejects_stale_witnesses_and_recomputes_progression_scope(self):
        work = search(2501,43,1)
        for changes,error in [
                ({'relation_verified':False},ValueError),({'height':0},ValueError),
                ({'anchor':work['anchor']+1},ValueError),({'stride':41},ValueError),
                ({'coefficients':[1,0,0,0,0]},ArithmeticError),
                ({'rootless_modulus':3},ValueError),({'rootless_modulus':101},ValueError)]:
            with self.subTest(changes=changes),self.assertRaises(error):
                extend(dict(work,**changes))
        sparse = search(2501,43,1,stride=3)
        result = extend(dict(sparse,covers_interval=True,progression_size=99),lower=40,upper=46)
        self.assertEqual(result['previous_progression_size'],3)
        self.assertTrue(result['progression_excluded'])
        self.assertFalse(result['covers_interval'] or result['excluded'])
        self.assertEqual(2501%41,0)
