import unittest
from math import gcd

from experiments.quartic_divisor_window import checked_height, evaluate, jet_basis, odd_quartile_center, search


class QuarticDivisorWindowTests(unittest.TestCase):
    def test_verified_progressions_match_direct_division(self):
        verified = partial = 0
        for n in (35,77,91,143,169,195,323,899,1763,2501):
            c = odd_quartile_center(n)
            for stride in (1,2,3):
                for w in (1,2):
                    if c <= stride*w or gcd(stride,n) != 1:
                        continue
                    r = search(n,c,w,stride=stride)
                    if not r['relation_verified']:
                        partial += 1
                        self.assertEqual((r['status'],r['excluded'],r['integer_root_nodes']),('partial',False,0))
                        continue
                    verified += 1
                    expected = [d for d in range(c-stride*w,c+stride*w+1,stride) if n%d==0]
                    self.assertEqual(r['divisors'],expected,(n,c,w,stride))
                    self.assertLess(r['height'],r['height_bound'])
                    self.assertEqual((c+stride*r['anchor'])%n,0)
                    self.assertTrue(all(evaluate(r['coefficients'],x)==0 for x in r['roots']))
                    if (p := r['rootless_modulus']) is not None:
                        self.assertTrue(all(evaluate(r['coefficients'],x)%p for x in range(p)))
                    if r['excluded']:
                        self.assertFalse(any(n%d==0 for d in range(r['lower'],r['upper']+1)))
        self.assertGreater(verified,20)
        self.assertGreater(partial,0)

    def test_integrality_and_strict_height_checks(self):
        for row in jet_basis(77,-25):
            self.assertGreater(checked_height(77,-25,2,row),0)
        for bad in ([1,0,0,0,0],[25,1,0,0,0]):
            with self.assertRaises(ArithmeticError):
                checked_height(77,-25,2,bad)
        with self.assertRaises(ValueError):
            checked_height(77,-25,2,[0]*5)
        failed = search(35,5,2,stride=1)
        self.assertGreaterEqual(failed['height'],failed['height_bound'])
        self.assertFalse(failed['progression_excluded'])

    def test_orientation_and_progression_scope(self):
        hit = search(2501,odd_quartile_center(2501),1)
        self.assertEqual(hit['hits'],[dict(offset=-1,divisor=41,cofactor=61)])
        # 41 lies in [40,46] but is outside the stride-three progression.
        other = search(2501,43,1,stride=3)
        self.assertTrue(other['progression_excluded'])
        self.assertFalse(other['excluded'])
        for n,c,w,s in ((91,15,1,7),(35,3,2,2),(35,5,0,2)):
            with self.assertRaises(ValueError):
                search(n,c,w,stride=s)
