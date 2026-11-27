from math import gcd, isqrt
import unittest

from experiments.merging_weight_intervals import count_overlaps, divisor_range, make_windows, merged, window
from experiments.rectangular_root_windows import bounds


class WeightWindowProjectionTests(unittest.TestCase):
    def test_exact_endpoints_on_rational_locations(self):
        for n in range(37,762,17):
            h=isqrt(n)//2
            budget=3*isqrt(n)
            for a,b,t in ((1,1,1),(1,3,1),(3,5,1),(1,2,2),(2,3,2)):
                result=window(n,budget,h,a,b,t,1,isqrt(n))
                got=[] if result is None else list(range(result[0],result[1]+1))
                expected=[d for d in range(1,isqrt(n)+1)
                          if t*abs(b*d*d-a*n)<=2*h*d and t*(b*d*d+a*n)<=2*budget*d]
                self.assertEqual(got,expected)

    def test_minimal_multiplicity_at_all_locations(self):
        for p,q in ((37,61),(47,59),(71,101),(137,191)):
            n=p*q
            lo,hi=divisor_range(n,p.bit_length())
            b,h,_=bounds(n,1)
            records,_=make_windows(n,p.bit_length())
            covered=merged(records)
            self.assertTrue(any(l<=p<=u for l,u in covered))
            for d in range(lo,hi+1):
                witnesses=[(a,big,t) for l,u,a,big,t in records if l<=d<=u]
                self.assertLessEqual(len(witnesses),2)
                if len(witnesses)==2:
                    (a,big,t),(c,dig,s)=witnesses
                    self.assertLess((big*d*d-a*n)*(dig*d*d-c*n),0)
                    self.assertLess(t*s,4)
                if gcd(d,n)==1 and d%2 and d>=h+1:
                    # Use a slightly wider ratio than needed in this independent brute force.
                    looked=False
                    for u in range(1,2*(b+h+2)//d+2):
                        for v in range(1,u+1):
                            if (u-v)%2==0 and abs(u*d*d-v*n)<2*(h+1)*d and u*d*d+v*n<=2*(b+1)*d:
                                looked=True
                                break
                        if looked:
                            break
                    self.assertTrue(looked)
            self.assertLessEqual(max(count_overlaps(records)),2)
