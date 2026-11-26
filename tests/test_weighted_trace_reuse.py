import unittest
from math import isqrt

from experiments.weighted_trace_reuse import components, search


class WeightedTraceReuseTests(unittest.TestCase):
    def test_exact_two_branches_including_square_boundaries(self):
        for n in (35, 77, 143):
            for a,b in ((1,1),(3,2),(5,3)):
                for stride in (2,24):
                    for z in range(1,100):
                        cost = {'boundary_roots': 0}
                        parts = components(n,a,b,z,1,80,cost,stride)
                        actual = [d for low,high in parts for d in range(low,high+1)]
                        expected = [d for d in range(1,81)
                                    if (z-stride)*d < a*d*d+b*n < (z+stride)*d]
                        self.assertEqual(actual,expected)
                        self.assertLessEqual(cost['boundary_roots'],2)

    def test_full_search_and_budget(self):
        for n in (392251*505537, 2501, 10403):
            for mode in ('fixed','connected','both','fixed24','connected24','both24','best24','hiary'):
                if n == 2501 and mode == 'hiary':
                    continue
                run = search(n,mode)
                expected = [d for d in range(run['lower'],isqrt(n)+1) if n % d == 0]
                self.assertEqual(run['divisors'],expected)
                self.assertTrue(run['full_cover'])
                capped = search(n,mode,max_setups=0)
                self.assertEqual(capped['work']['setups'],0)
                self.assertEqual(capped['prefix_covered'],0)
                self.assertFalse(capped['full_cover'])


if __name__ == '__main__':
    unittest.main()
