import unittest
from itertools import combinations, product
from math import gcd, prod

from experiments.gap_coverage import primes_through
from experiments.reciprocal_wheel import band, ordinary, search


def direct(n, w, width, cap):
    low, high = band(n)
    retained = []
    minimum = 0
    for start in range(low, min(high+1, low+cap*width), width):
        end = min(high+1, start+width)
        upper = list(range((n+end-2)//(end-1), n//start+1))
        classes = {y % w for y in upper}
        for x in range(start, end):
            if gcd(x,w) == 1 and n*pow(x,-1,w)%w in classes:
                retained.append(x)
        for r in range(w):
            if gcd(r,w) == 1:
                count = sum(x%w == r for x in range(start,end))
                opposite = sum(y%w == n*pow(r,-1,w)%w for y in upper)
                minimum += min(count, opposite)
    return retained, minimum


class ReciprocalWheelTests(unittest.TestCase):
    def test_grouped_product_and_minimum_against_direct_rectangles(self):
        for n, w in product((77,101*149,105*107), (1,6,8,13,30)):
            if gcd(n,w) > 1:
                continue
            for width in {1, min(4,w), w}:
                for limit in (0,2,1000):
                    rows, optimum = direct(n,w,width,limit)
                    answer = search(n,w,width,limit)
                    self.assertEqual(int(answer['product']), prod(rows)%n)
                    self.assertEqual(answer['compatible_candidates'], optimum)
                    self.assertEqual(optimum,len(rows))

    def test_both_complete_gcds_return_the_smaller_factor(self):
        for p,q in combinations(primes_through(70)[1:],2):
            if q > 2*p:
                continue
            for w in (1,6,10,31):
                if gcd(w,p*q) > 1:
                    continue
                paired = search(p*q,w,min(w,5),1000)
                plain = ordinary(p*q,w)
                self.assertTrue(paired['complete'])
                self.assertEqual(paired['factor'],p)
                self.assertEqual(plain['factor'],p)
                low, high = band(p*q)
                expected = prod(x for x in range(low, high+1) if gcd(x,w)==1) % (p*q)
                self.assertEqual(int(plain['product']),expected)

    def test_inputs_and_small_example(self):
        for args in ((15,5,3,2), (15,2,3,1), (15,2,2,-1)):
            with self.assertRaises(ValueError):
                search(*args)
        result = search(15049,30,7,6)
        self.assertEqual((result['ordinary_candidates'], result['compatible_candidates'],
                          result['factor']), (10,3,101))
