from collections import Counter
from itertools import islice
from math import gcd, isqrt
import unittest

from experiments.rectangular_root_windows import product_count_bound
from experiments.rectangular_weight_streams import POLICIES, eager_lanes, scan, stream


class RectangularWeightStreamsTests(unittest.TestCase):
    def test_order_and_coverage(self):
        for cap in (0,1,2,7,8,31,100,511,2048):
            for scale,excess in ((1,0),(100,1),(100,53),(1,1),(1,4)):
                with self.subTest(cap=cap, scale=scale, excess=excess):
                    expected = []
                    descriptors = 0
                    for t in (1,4):
                        for a in range(1,isqrt(cap//t)+1):
                            if t==1 and a%2==0:
                                continue
                            lane = [b for b in range(a,cap//(t*a)+1)
                                    if scale*b<=(scale+excess)*a
                                    and (b%2==1 if t==1 else a%2!=b%2)]
                            descriptors += bool(lane)
                            expected.extend(t*a*b for b in lane if gcd(a,b)==1)
                    eager,lazy,direct = (list(stream(p,cap,scale,excess,Counter())) for p in POLICIES)
                    self.assertEqual(descriptors,eager_lanes(cap,scale,excess))
                    self.assertEqual(direct,expected)
                    self.assertEqual(lazy,sorted(set(expected)))
                    self.assertEqual(lazy,eager)
                    self.assertLessEqual(len(direct),product_count_bound(cap,scale,excess))

    def test_uncapped_lazy_start(self):
        work = Counter()
        first = list(islice(stream("lazy_sorted",1<<680,100,0,work),2))
        self.assertEqual(first,[1])
        self.assertEqual(work["lane_starts"],1)
        prefix = list(islice(stream("lazy_sorted",1<<680,100,7,work),32))
        small = list(islice(stream("eager_sorted",20000,100,7,Counter()),32))
        self.assertEqual(prefix,small)
        self.assertLess(work["peak_lanes"],32)

    def test_pair_order_includes_real_duplicates(self):
        direct = list(stream("pair_order",5000,100,100,Counter()))
        self.assertGreater(len(direct),len(set(direct)))
        self.assertTrue(any(x>y for x,y in zip(direct,direct[1:])))

    def test_positive_rows(self):
        for n,bits,pair in ((37*61,6,["37","61"]),(43*47,6,["43","47"])):
            for name in POLICIES:
                result,_ = scan(n,bits,name)
                self.assertEqual(result["first"]["pair"],pair)
                self.assertGreater(result["work"]["row_gcds"],0)
