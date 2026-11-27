from fractions import Fraction
from math import gcd
import unittest

from experiments.rectangular_root_windows import bounds, interval
from experiments.rectangular_winning_rows import bracket, observation
from scripts.factor import primes_through


class WinningRowTests(unittest.TestCase):
    def test_fraction_neighbors_match_exhaustive_order(self):
        for n in range(3, 28):
            for r in range(1, n):
                if gcd(r, n) != 1:
                    continue
                for cap in (1, n//2, n-1):
                    (left, right), _ = bracket(r, n, cap)
                    fractions = [Fraction(a, b) for b in range(1, cap+1) for a in range(b+1)]
                    target = Fraction(r,n)
                    self.assertEqual(Fraction(*left[:2]), max(v for v in fractions if v < target))
                    self.assertEqual(Fraction(*right[:2]), min(v for v in fractions if v > target))

    def test_primitive_and_scaled_rows_match_exhaustive_scan(self):
        from math import isqrt
        primes = [p for p in primes_through(83) if p>3]
        for i, p in enumerate(primes):
            for q in primes[i+1:]:
                n = p*q
                b,h,limit = bounds(n,1)
                if h>=p or b+h>=n:
                    continue
                got = observation(p,q)
                expected = set()
                for k in range(1,limit+1):
                    lo,hi = interval(n,1,k,b,h)
                    for y in range(lo,hi+1):
                        x = isqrt(y*y-k*n)
                        if x*x == y*y-k*n:
                            expected.add((k,x,y))
                actual = {(int(w['multiplier'])*g*g, int(w['x'])*g, int(w['y'])*g)
                          for w in got['neighbors'] if w['inside'] for g in range(1,int(w['scales'])+1)}
                self.assertEqual(actual,expected,(p,q))
