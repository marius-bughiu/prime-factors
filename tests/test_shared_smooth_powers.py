from itertools import combinations
from math import gcd, prod
import unittest

from experiments.shared_smooth_powers import (
    accepted_seed, batch_factor, classical_scan, schedule, shared_powers, shared_scan, window_power,
)
from scripts.factor import primes_through


def counters():
    return dict(squares=0, multiplies=0, prefix_blocks=0, prefix_gcds=0, tail_powers=0, batch_gcds=0)


class SharedSmoothPowers(unittest.TestCase):
    def test_coverage_of_every_order_below_small_caps(self):
        for bits in range(1,11):
            for bound in (2,3,7,19,50):
                blocks = schedule(bound,bits)
                whole = prod(h for _,_,_,h in blocks)
                low = prod(a for _,a,_,_ in blocks)
                for d in range(1,2**bits):
                    self.assertEqual(whole % d == 0,
                                     low % d == 0 or any(low*t % d == 0 for _,_,t,_ in blocks))

    def test_counted_powers(self):
        for n in (21,221,65537):
            exponents = list(range(1,180)) + [2**1038, 3**512, 13**77]
            for z in (0,2,5,n-1):
                expected = [pow(z,e,n) for e in exponents]
                self.assertEqual(shared_powers(z,exponents,n,counters()),expected)
                self.assertEqual([window_power(z,e,n,counters()) for e in exponents],expected)
        self.assertEqual(shared_powers(2,[],9,counters()),[])

    def test_saturated_tree_with_unpaired_nodes(self):
        for size in range(2,16):
            for i,j in combinations(range(size),2):
                values = [2]*size
                values[i], values[j] = 8,12  # one difference divisible by 7, the other by 11
                work = counters()
                self.assertIn(batch_factor(77,values,work),(7,11))
                self.assertEqual(work['multiplies'],size-1)
                self.assertLessEqual(work['batch_gcds'],1+(size-1).bit_length())

    def test_identical_success_for_all_small_accepted_bases(self):
        for p,q in combinations(primes_through(45)[1:],2):
            n = p*q
            for a in range(2,min(15,n)):
                seed = pow(a,n-1,n)
                if gcd(a,n)!=1 or seed==1:
                    continue
                for bound in (2,5,11,29):
                    plan = schedule(bound,q.bit_length())
                    z = pow(seed,prod(h for _,_,_,h in plan),n)
                    should_split = gcd(z-1,n)>1
                    actual,_ = shared_scan(n,seed,plan,counters())
                    self.assertEqual(actual in (p,q),should_split)
                    for fused in (False,True):
                        control,_ = classical_scan(n,seed,plan,fused)
                        self.assertEqual(control in (p,q),should_split)

    def test_base_budget_and_worst_case_counts(self):
        self.assertEqual(accepted_seed(341,2)[:3],(None,None,None))
        self.assertEqual(accepted_seed(6,4)[0],2)
        for bound,expected,floor in ((100,19821,25546),(1000,123531,171327)):
            plan = schedule(bound,1024)
            work = counters()
            for _,low,_,_ in plan:
                window_power(2,low,101,work)
            values = shared_powers(2,[t for _,_,t,_ in plan if t>1],101,work)
            batch_factor(101,values,work)
            self.assertEqual(work['squares']+work['multiplies'],expected)
            self.assertEqual((prod(h for _,_,_,h in plan)-1).bit_length(),floor)
            self.assertLess(expected,floor)
