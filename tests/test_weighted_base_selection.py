from itertools import combinations
from math import lcm
import unittest

from experiments.gap_coverage import primes_through
from experiments.weighted_base_selection import search, select
from experiments.weighted_stride_search import search as fixed_search


def local_order(base, stride, p):
    h = pow(base, stride, p)
    power = h
    for i in range(1, p):
        if power == 1:
            return i
        power = power*h % p


class WeightedBaseSelectionTests(unittest.TestCase):
    def test_two_rejected_bases_combine(self):
        n = 32817151
        for beta, expected in [(2,25), (3,135)]:
            self.assertEqual(fixed_search(n,4,136,1000,beta=beta)['outcome'], 'short_order')
            self.assertEqual([local_order(beta,24,p) for p in (4051,8101)], [expected]*2)
        result = search(n,4,136,1000,prime_limit=3)
        self.assertEqual((result['factor'], result['outcome']), (4051,'trace_divisor'))
        self.assertEqual(result['selection']['selected_base'], 486)
        self.assertEqual(result['selection']['work']['combined_order'], '675')
        self.assertEqual([local_order(486,24,p) for p in (4051,8101)], [675,675])

    def test_prefix_selection_matches_element_orders(self):
        for p, q in combinations(primes_through(73)[2:], 2):
            if q > 2*p:
                continue
            for stride in (1,24):
                for m in (1,5,12):
                    result = select(p*q,m,prime_limit=11,stride=stride)
                    work = result['work']
                    accumulated = 1
                    for beta, r in work['short_orders']:
                        self.assertEqual([local_order(beta,stride,s) for s in (p,q)], [r,r])
                        new = lcm(accumulated, r)
                        self.assertGreaterEqual(new, 2*accumulated)
                        accumulated = new
                    self.assertEqual(int(work['combined_order']), accumulated)
                    if result['factor'] is not None:
                        self.assertIn(result['factor'], (p,q))
                    elif result['selected_base'] is not None:
                        for s in (p,q):
                            self.assertGreaterEqual(local_order(result['selected_base'],stride,s), m)
                    else:
                        self.assertEqual(result['outcome'], 'prime_limit')
                        for base in (2,3,5,7,11):
                            self.assertEqual(accumulated % local_order(base,stride,p), 0)

    def test_redundancy_refinement_and_caps(self):
        result = select(32817151,676,prime_limit=11)
        self.assertEqual(result['outcome'], 'prime_limit')
        self.assertEqual((result['work']['order_scans'],result['work']['redundant_bases']), (2,3))
        self.assertEqual(select(77,8,prime_limit=5)['outcome'], 'exponent_divisor')
        self.assertEqual(select(35,5,prime_limit=2,stride=1)['outcome'], 'order_divisor')
        self.assertEqual(select(35,2,prime_limit=5)['outcome'], 'base_divisor')
        self.assertEqual(select(32817151,136,prime_limit=3,max_primes=1)['outcome'], 'prime_count_limit')
        self.assertEqual(select(32817151,1000,max_babies=50)['outcome'], 'baby_limit')
