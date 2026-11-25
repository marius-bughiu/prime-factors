from itertools import product
from math import gcd
import unittest

from experiments.offset_prime_power_slopes import (
    all_power_lower, choose_powers, local_count, reconstruct, search, verify_charts,
)
from scripts.factor import primes_through


class PrimePowerSlopeTests(unittest.TestCase):
    def test_local_normalizations_and_exact_counts(self):
        self.assertEqual(verify_charts(),124)
        self.assertEqual([local_count(3,e,True) for e in range(1,7)],[3,5,13,35,103,305])

    def test_reconstruction_with_nonzero_nonunit_coordinates(self):
        for powers,j_limit,k_limit in [([(3,3),(5,2)],17,18), ([(3,3),(5,2)],8,41),
                                       ([(3,2),(7,2)],18,12)]:
            moduli = [p**e for p,e in powers]
            charts = [[(a,1) for a in range(q)]+[(1,b) for b in range(0,q,p)]
                      for q,(p,_) in zip(moduli,powers)]
            recovered = set()
            for dirs in product(*charts):
                point = reconstruct(moduli,dirs,j_limit,k_limit)
                if point is None:
                    continue
                j,k = point
                self.assertTrue(all((b*j-a*k)%q==0 for q,(a,b) in zip(moduli,dirs)))
                self.assertNotIn(point,recovered)
                recovered.add(point)
            expected = {(j,k) for j in range(1,j_limit+1) for k in range(1,k_limit+1) if gcd(j,k)==1}
            self.assertEqual(recovered,expected)

    def test_all_power_bound_against_independent_exhaustion(self):
        for n in (101,103):
            primes = primes_through(97)[1:]
            signs = {p: pow(n,(p-1)//2,p)==1 for p in primes}
            for threshold in (20,65,110):
                # From 12*G>=5*p^e, every local component costing <=40
                # has modulus <=96. Thus a complete wheel costing <=40
                # uses only the finite components enumerated here.
                best = 40
                def visit(start,m,g):
                    nonlocal best
                    if m>threshold:
                        best = min(best,g)
                        return
                    for i in range(start,len(primes)):
                        p = primes[i]
                        e = 1
                        while p**e<=96:
                            price = g*local_count(p,e,signs[p])
                            if price<=best:
                                visit(i+1,m*p**e,price)
                            e += 1
                visit(0,1,1)
                cert = all_power_lower(primes[:6],signs,threshold,40,conditioned=3)
                self.assertLessEqual(cert['lower'],best)

    def test_selected_search_and_partial_accounting(self):
        result = search(1776168403,8073,exhaust=True)
        self.assertEqual(result['hits'],[(124,63,53959)])
        self.assertEqual((result['visited'],result['unchecked'],result['square_tests']),(8073,0,597))
        self.assertEqual([(p,e) for p,e in result['powers'] if e>1],[(3,3),(7,2)])
        partial = search(1776168403,0)
        self.assertEqual((partial['status'],partial['remaining'],partial['unchecked']),('partial',1776168403,8073))
        self.assertEqual(choose_powers(3*19,4,6),dict(factor=3))
