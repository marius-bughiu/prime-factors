from collections import Counter
from math import gcd, isqrt
import unittest

from experiments.rectangular_root_windows import (
    bounds, candidate_bound, interval, product_count_bound, run, small_check, weight_products,
)
from experiments.rectangular_weight_panel import check_small


class RectangularWindowTests(unittest.TestCase):
    def test_all_recoverable_root_classes(self):
        self.assertEqual(small_check(), {'products': 126, 'root_classes': 438})
        self.assertEqual(check_small(), {'products': 111, 'rows_removed': 1434})

    def test_closed_interval_endpoints(self):
        for n in (35, 77, 119, 221, 3071):
            for d in (-6, -3, -2, -1, 1, 2, 3, 6):
                b, h, last = bounds(n,d)
                count = 0
                for k in range(1,last+1):
                    low,high=interval(n,d,k,b,h)
                    offset = k*n if d < 0 else -k*n
                    direct = [y for y in range(1,b+1) if 0 <= d*y*y+offset <= h*h]
                    self.assertEqual(direct,list(range(low,high+1)))
                    count += len(direct)
                self.assertLessEqual(count,candidate_bound(n,d)[1])

    def test_weight_lanes_deduplicate_and_respect_rational_ratio(self):
        for cap in (1, 2, 8, 64, 1007):
            for excess in (0, 1, 31, 170):
                expected = set()
                for k in range(1,cap+1):
                    for t in (1,4):
                        if k%t:
                            continue
                        for a in range(1,isqrt(k//t)+1):
                            b,r=divmod(k//t,a)
                            if r or gcd(a,b)!=1 or 100*b>(100+excess)*a:
                                continue
                            if (t==1 and a%2==b%2==1) or (t==4 and a%2!=b%2):
                                expected.add(k)
                output=list(weight_products(cap,100,excess,Counter()))
                self.assertEqual(output,sorted(expected))
                self.assertLessEqual(len(output),product_count_bound(cap,100,excess))

    def test_zero_budget_and_single_remaining_cofactor(self):
        result=run(3071,[1],rows=0,per_row=1)
        self.assertIsNone(result['factor'])
        self.assertEqual(result['work']['rows'],0)
        self.assertFalse(result['intervals_finished'])
        result=run(3071,[1],per_row=0)
        self.assertEqual(result['work']['coordinates'],0)
        self.assertGreater(result['work']['truncated_positions'],0)
