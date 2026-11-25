from collections import Counter
from math import gcd,isqrt
import unittest

from experiments.offset_lattice_batches import search
from experiments.offset_row_norm import compare,rules


class OffsetRowNormTests(unittest.TestCase):
    def test_locally_soluble_empty_integral_row(self):
        for q in range(2,91):
            residues={z*z%q for z in range(q)}
            self.assertTrue(any((-71*w*w+212*w-88)%q in residues
                                and gcd(gcd(w,2*w-1),q)==1 for w in range(q)))
        self.assertEqual([-71*w*w+212*w-88 for w in range(-10,11)
                          if -71*w*w+212*w-88>=0],[53,52])

    def test_shell_uses_the_lattice_determinant(self):
        # D(2,1)=36 at N=91. With determinant 3 an index not divisible
        # by three lies at exact 3-adic distance one from this pivot.
        multiples,shells=rules(91,9,10,(2,1),3,[3],8)
        self.assertEqual((multiples,shells),([],[(1,3)]))
        for u in (1,2,-1,-2):
            for w in range(-15,16):
                j,k=2*w-3*u,w
                if gcd(j,k)==1:
                    delta=j*j+4*k*(9*j-10*k)
                    self.assertEqual(delta%3,0)
                    self.assertNotEqual(delta%9,0)

    def test_rejected_rows_have_no_primitive_square(self):
        n=221
        t=isqrt(n);h=n-t*t
        rejected=Counter()
        for x in [(1,0),(0,1),(2,1),(4,2),(-1,3),(3,-1)]:
            a,b=x
            for c,d in [(0,1),(1,1),(-2,3),(5,2),(-3,4)]:
                det=a*d-b*c
                if det<=0:
                    continue
                multiples,shells=rules(n,t,h,x,det,[2,3,5,7,11],12)
                for u in (*range(-12,0),*range(1,13)):
                    why='scaled' if any(u%q==0 for q in multiples) else (
                        'shell' if any(u%q==0 and u%r!=0 for q,r in shells) else None)
                    if why is None:
                        continue
                    rejected[why]+=1
                    for w in range(-12,13):
                        j,k=a*w+c*u,b*w+d*u
                        delta=j*j+4*k*(t*j-h*k)
                        self.assertFalse(gcd(j,k)==1 and delta>=0 and isqrt(delta)**2==delta)
        self.assertTrue(rejected['scaled'])

    def test_normal_path_skips_the_independently_replayed_work(self):
        n=3376036549
        replay=compare(n)
        baseline=search(n,10000,drop=2,exhaust=True)
        new=search(n,10000,drop=2,exhaust=True,primitive_rows=True)
        self.assertEqual((baseline['factor'],baseline['remaining'],baseline['proper_hits']),
                         (new['factor'],new['remaining'],new['proper_hits']))
        self.assertEqual(new['point_visits'],replay['retained_positions'])
        self.assertEqual(new['square_tests'],replay['retained_sqrt'])
        self.assertEqual(baseline['square_tests']-new['square_tests'],52)
        self.assertEqual((new['valuation_rejections'],new['unfinished_batches']),(32,0))
