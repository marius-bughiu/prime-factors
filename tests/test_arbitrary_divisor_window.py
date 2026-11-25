import unittest
from math import isqrt

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
