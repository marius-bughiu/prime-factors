import unittest
from math import isqrt

from experiments.shared_multiplier_prefix import divisors, merge, search


class SharedMultiplierTests(unittest.TestCase):
    def test_shared_geometry_against_literal_interval(self):
        for n in (77,143,323,899,2501,10403):
            for k in (1,4,6,24,180):
                for cap in (1,4,9):
                    result = search(n,k,cap)
                    shared = result['shared']
                    low,high,t = result['lower'],result['upper'],result['first_omitted']
                    wanted = {x for x in range(low,high+1) if any(a*x*x+(k//a)*n < t*x
                                                                  for a in divisors(k))}
                    got = {x for lo,hi in shared['intervals'] for x in range(lo,hi+1)}
                    self.assertEqual(wanted, got)
                    self.assertEqual(shared['positions'],len(wanted))
                    self.assertEqual(shared['factors'],[x for x in sorted(wanted) if 1<x<n and n%x==0])
                    self.assertEqual(shared['work']['trace_square_tests'], cap)
                    self.assertEqual(shared['work']['hull_roots'],1)

    def test_discovery_and_comparisons(self):
        run = search(2113561)
        self.assertEqual(run['shared']['directions'],576)
        self.assertEqual(run['shared']['gcd_splits'],[1051])
        self.assertEqual(run['shared']['factors'],[1051])
        self.assertEqual(run['shared']['widest_factors'],[])
        self.assertEqual(run['ordinary_mod24']['gcd_splits'],[])
        self.assertEqual(run['shared']['squares'],[(13520145,6225)])
        self.assertEqual(search(32881)['ordinary_mod24']['gcd_splits'],[131])

    def test_integral_boundary_and_merging(self):
        self.assertEqual(merge([(1,4),(3,5),(7,9),(10,12)]),[(1,5),(7,12)])
        result = search(49,1,1)
        self.assertEqual(result['first_trace'],14)
        self.assertEqual(result['shared']['factors'],[7])
        self.assertEqual(isqrt(4*49),14)


if __name__ == '__main__':
    unittest.main()
