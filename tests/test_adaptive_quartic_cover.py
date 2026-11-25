import unittest

from experiments.adaptive_quartic_cover import bernstein, level_range, search
from experiments.quartic_divisor_window import evaluate


class AdaptiveQuarticCoverTests(unittest.TestCase):
    def test_integer_level_bounds_on_signed_and_singleton_offsets(self):
        for center in (11,25):
            square = [center**2,4*center,4,0,0]
            for left,right in ((-5,-5),(-4,-1),(-3,5),(0,1),(1,9)):
                denominator = bernstein(square,left,right)
                self.assertGreater(min(denominator),0)
                for row in ([77,-11,0,6,5],[-45,75,0,-17,-2],[-v for v in square],square):
                    lo,hi = level_range(row,left,right,denominator)
                    for x in range(left,right+1):
                        d2 = (center+2*x)**2
                        value = evaluate(row,x)
                        self.assertLess((lo-1)*d2,value)
                        self.assertLess(value,(hi+1)*d2)

    def test_contiguous_prefix_agrees_with_trial_division(self):
        for n in (2501,22663,1009*1499,997*839,751*997,359*449,131**2,31**3):
            for mode in ('single','joint'):
                for cap in (0,1,100):
                    r = search(n,full=True,max_reductions=cap,mode=mode)
                    start,count = r['start_odd'],r['covered_odd_positions']
                    expected = [d for d in range(start,start+2*count,2) if n%d==0]
                    self.assertEqual(r['divisors'],expected)
                    total = (r['last_odd']-r['first_odd'])//2+1
                    self.assertEqual(r['unvisited_odd_positions']+count,total)
                    self.assertEqual(r['schedule_exhausted'],count==total)
                    self.assertEqual(r['work']['covered_chunks'],
                                     r['work']['empty_level_chunks']+r['work']['modular_chunks']
                                     +r['work']['sieved_level_chunks']+r['work']['root_checked_chunks'])
                    self.assertLessEqual(r['work']['lll_calls'],cap)

    def test_joint_receipt_by_independent_modular_enumeration(self):
        n = 502005281288939
        r = search(n,full=True,max_reductions=40,sample_certificate=True)
        cert = r['sample_certificate']
        self.assertIsNotNone(cert)
        rows = cert['rows']
        p = cert['modulus']
        c = cert['center']
        self.assertGreater(len(rows),1)
        self.assertTrue(any(row['low']<row['high'] for row in rows))
        self.assertGreater(cert['left'],r['radius'])
        self.assertEqual((c+2*cert['anchor'])%n,0)
        square = [c*c,4*c,4,0,0]
        for row in rows:
            for x in range(cert['left'],cert['right']+1):
                d2 = (c+2*x)**2
                value = evaluate(row['coefficients'],x)
                self.assertLess((row['low']-1)*d2,value)
                self.assertLess(value,(row['high']+1)*d2)
        permitted = {x for x in range(p) if (c+2*x)%p}
        options = [{x for x in permitted if any(
            (evaluate(row['coefficients'],x)-k*evaluate(square,x))%p==0
            for k in range(row['low'],row['high']+1))} for row in rows]
        self.assertTrue(all(options))
        self.assertFalse(set.intersection(*options))

    def test_rejects_invalid_budgets(self):
        for params in (dict(max_reductions=-1),dict(max_reductions=1,level_cap=0),
                       dict(max_reductions=1,chunks_per_basis=0),dict(max_reductions=1,mode='unknown')):
            with self.assertRaises(ValueError):
                search(2501,full=True,**params)
