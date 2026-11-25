import unittest
from math import gcd, isqrt

from experiments.arbitrary_divisor_window import quartile_center, search


class ArbitraryDivisorWindowTests(unittest.TestCase):
    def test_small_windows_against_all_divisors(self):
        locations = set()
        for n in range(5,251,2):
            for c in range(2,isqrt(n)+1):
                for w in range(1,min(c,5)):
                    try:
                        result = search(n,c,w)
                    except ValueError:
                        # Even the largest allowed denominator guarantees
                        # coverage whenever this product-only condition holds.
                        self.assertGreater(2*w*n*w*w,c*c*(c-w))
                        continue
                    a,b = result['a'],result['b']
                    self.assertTrue(1 <= b <= 2*w)
                    self.assertLessEqual(abs(a*c*c-b*n)*(2*w+1),c*c)
                    self.assertLessEqual(b*n*w*w,c*c*(c-w))
                    expected = [d for d in range(c-w,c+w+1) if n%d==0]
                    self.assertEqual(result['divisors'],expected,(n,c,w))
                    self.assertEqual(result['excluded'],not expected)
                    for d in expected:
                        self.assertEqual(result['trace'],a*d+b*(n//d))
                    self.assertLessEqual(result['square_tests'],1)
                    self.assertLessEqual(result['candidate_tests'],2)
                    locations.add(result['stationary_point'])
        self.assertEqual(locations,{'interior','at_or_above_upper','at_or_below_lower'})

    def test_quartile_example_and_both_signs(self):
        self.assertEqual(quartile_center(2501),42)
        hit = search(2501,42,2)
        self.assertEqual(hit['hits'],[dict(trace=245,divisor=41,cofactor=61)])
        both = search(45,4,1)
        self.assertEqual(both['divisors'],[3,5])
        square = search(9,3,1)
        self.assertEqual((square['candidate_tests'],square['divisors']),(1,[3]))
        # A square discriminant can still have no oriented divisor in the window.
        miss = search(39,5,1)
        self.assertEqual((miss['candidate_tests'],miss['divisor_tests'],miss['excluded']),(2,1,True))

    def test_clipping_and_validation(self):
        clipped = search(11,3,1)
        self.assertEqual((clipped['possible_traces'],clipped['square_tests'],clipped['excluded']),(0,0,True))
        for args in ((10,3,1),(11,4,1),(11,3,0),(11,3,3),(101,10,5)):
            with self.assertRaises(ValueError):
                search(*args)

    def test_mod24_windows_against_direct_division(self):
        locations, residues, hit_counts = set(), set(), set()
        for d in range(185,231,2):
            for q in range(d,2*d,10):
                n = d*q
                if gcd(n,6) != 1:
                    continue
                for c in {d-4,d,d+5,isqrt(n)-2}:
                    if c*c > n:
                        continue
                    for w in (6,7,8):
                        result = search(n,c,w,mod24=True)
                        a,b,t = result['a'],result['b'],result['trace']
                        expected = [x for x in range(c-w,c+w+1) if n%x == 0]
                        self.assertEqual(result['divisors'],expected,(n,c,w))
                        self.assertEqual(t%24,(a+b*n)%24)
                        self.assertEqual((a+b*n)%12,0)
                        self.assertLessEqual(abs(a*c*c-b*n)*(2*w+1),12*c*c)
                        self.assertLessEqual(b*n*w*w,12*c*c*(c-w))
                        self.assertTrue(all(a*x+b*(n//x)==t for x in expected))
                        self.assertLessEqual(result['candidate_tests'],2)
                        locations.add(result['stationary_point'])
                        residues.add(t%24)
                        hit_counts.add(len(expected))
        self.assertEqual(locations,{'interior','at_or_above_upper','at_or_below_lower'})
        self.assertEqual(residues,{0,12})
        self.assertEqual(hit_counts,{0,1,2})

    def test_mod24_wider_window_and_guard(self):
        hit = search(87097,255,8,mod24=True)
        self.assertEqual((hit['trace_stride'],hit['a'],hit['b'],hit['trace']),(24,7,5,3492))
        self.assertEqual(hit['hits'],[dict(trace=3492,divisor=251,cofactor=347)])
        self.assertEqual((hit['candidate_tests'],hit['divisor_tests']),(2,1))
        repeated = search(121,11,3,mod24=True)
        self.assertEqual((repeated['candidate_tests'],repeated['divisors']),(1,[11]))
        with self.assertRaisesRegex(ValueError,'coprime to six'):
            search(45,4,1,mod24=True)
        with self.assertRaisesRegex(ValueError,'positive weights'):
            search(25,5,1,mod24=True)
        with self.assertRaisesRegex(ValueError,'curvature bound'):
            search(87097,255,200,mod24=True)
