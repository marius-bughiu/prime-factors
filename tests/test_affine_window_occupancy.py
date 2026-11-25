from math import gcd, isqrt
import unittest

from experiments.affine_window_occupancy import approximant, count, lane, sample, witness


class AffineWindowOccupancyTests(unittest.TestCase):
    def test_all_small_counts_match_direct_products(self):
        for n in (*range(3,160,2), 1225, 10403):
            for r in (2, 4, 8, 16):
                totals = [0]*r
                for x in range(max(2,isqrt((n-1)//2)+1),isqrt(n)+1):
                    for y in range(isqrt(n-1)+1,isqrt(2*n)+1):
                        if (x*y-n) % (r*r) == 0:
                            totals[x%r] += 1
                for u in range(1,r,2):
                    self.assertEqual(count(n,r,u)[0],totals[u])

    def test_covering_certificate_across_rational_slopes(self):
        for r in (8, 16, 32, 64, 128):
            for a in range(r):
                for h in (1,2,4,8):
                    p,q = approximant(a,r,h)
                    self.assertGreaterEqual(q,1)
                    self.assertLessEqual(q,h)
                    self.assertEqual(gcd(p,q),1)
                    self.assertLessEqual(abs(a*q-r*p)*h,r)
                    if q*h < r:
                        continue
                    for ycenter in (-37,-1,0,53,2*r):
                        xstart, c = -11, 31
                        t = (ycenter-c-a*xstart)*q//r
                        v = t*pow(p,-1,q)%q
                        y = c+a*(xstart+v)-r*((p*v-t)//q)
                        self.assertLessEqual(abs(y-ycenter),h+r//h)
                        self.assertEqual((y-c-a*(xstart+v))%r,0)

    def test_guaranteed_witness_in_balanced_interval(self):
        n, r, h = (1 << 160)+98765, 1<<48, 1<<27
        for u in sample(n,r,32):
            w,a,_,x0,x1,y0,y1 = lane(n,r,u)
            xy = witness(n,r,u,h)
            _,q = approximant(a,r,h)
            if q >= r//h:
                self.assertIsNotNone(xy)
            if xy is not None:
                x,y = xy
                self.assertLessEqual(x0,(x-u)//r)
                self.assertLess((x-u)//r,x1)
                self.assertLessEqual(y0,(y-w)//r)
                self.assertLess((y-w)//r,y1)
                self.assertEqual((x*y-n)%(r*r),0)
