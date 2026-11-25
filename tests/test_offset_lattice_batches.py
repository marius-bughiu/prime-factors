"""Compare the partial wheel's row enumeration with direct integer and full-wheel scans."""

from collections import Counter
from itertools import product
from math import gcd, prod
import unittest

from experiments.offset_crt_reconstruction import search as full_search
from experiments.offset_lattice_batches import batch_events, direction_basis, line_basis, search


class OffsetLatticeBatchTests(unittest.TestCase):
    def test_each_tuple_recovers_exactly_its_primitive_ragged_points(self):
        primes = (5,7)
        j_limit,k_limit,t,h = 20,19,8,11
        all_observed = set()
        for slopes in product(*(tuple(range(p))+(None,) for p in primes)):
            x,y = line_basis(primes,slopes,j_limit,k_limit,Counter())
            events = list(batch_events(x,y,j_limit,k_limit,t,h))
            points = [z for kind,z in events if kind=='point']
            self.assertLessEqual(len(points),2+4*j_limit*k_limit//prod(primes))
            observed = {(j,k) for j,k in points if gcd(j,k)==1}
            expected = {(j,k) for j in range(1,j_limit+1) for k in range(1,min(k_limit,t*j//h+1)+1)
                        if gcd(j,k)==1 and all((k%p==0 if slope is None else (j-slope*k)%p==0)
                                              for p,slope in zip(primes,slopes))}
            self.assertEqual(expected,observed)
            self.assertTrue(all_observed.isdisjoint(observed))
            all_observed.update(observed)

    def test_axis_has_constant_cost_even_in_long_thin_box(self):
        events = list(batch_events((1,1),(0,10**7),10000,10000,3,2))
        self.assertEqual(events,[('row',False),('point',(1,1))])

    def test_prime_power_lines_include_nonunit_reverse_coordinates(self):
        j_limit,k_limit,t,h = 28,31,13,11
        for entry in ((1,0),(1,2),(1,4),(1,6),(2,1)):
            directions = (entry,(3,1))
            moduli = (8,5)
            x,y = direction_basis(moduli,directions,j_limit,k_limit,Counter())
            self.assertEqual(x[0]*y[1]-x[1]*y[0],prod(moduli))
            actual = {value for kind,value in batch_events(x,y,j_limit,k_limit,t,h)
                      if kind == 'point' and gcd(*value) == 1}
            expected = {(j,k) for j in range(1,j_limit+1)
                        for k in range(1,min(k_limit,t*j//h+1)+1) if gcd(j,k)==1
                        and all((b*j-a*k)%q == 0 for (a,b),q in zip(directions,moduli))}
            self.assertEqual(actual,expected)

    def test_dyadic_batches_complete_both_charts_and_share_one_budget(self):
        for n,expected_parity in ((117449,0),(134683853,1)):
            odd = search(n,1<<16,drop=2,exhaust=True)
            both = search(n,1<<16,drop=2,exhaust=True,dyadic_exponent=8)
            self.assertEqual(both['first_hit'],odd['first_hit'])
            self.assertEqual(both['first_hit'][1] % 2,expected_parity)
            self.assertEqual(both['proper_hits'],odd['proper_hits'])
            self.assertEqual(both['unfinished_batches'],0)
            charts = both['charts']
            forward = charts['forward']['total_batches']
            self.assertEqual(both['total_batches'],forward + charts['reverse']['total_batches'])
            clipped = search(n,forward,drop=2,exhaust=True,dyadic_exponent=8)
            self.assertEqual(clipped['charts']['reverse']['started_batches'],0)
            self.assertEqual(clipped['unfinished_batches'],charts['reverse']['total_batches'])

    def test_complete_search_and_row_filter_preserve_every_split(self):
        for n in (9017,117449,134683853):
            reference=full_search(n,1<<16,exhaust=True,optimize_wheel=True)
            for drop in (0,1,2):
                for sieve in (True,False):
                    run=search(n,1<<16,exhaust=True,drop=drop,row_sieve=sieve)
                    self.assertEqual(run['unfinished_batches'],0)
                    self.assertEqual(run['proper_hits'],reference['proper_hits'])
                    self.assertEqual({run['factor'],run['remaining']},{reference['factor'],reference['remaining']})
                    if not sieve:
                        self.assertEqual(run['square_tests'],reference['square_tests'])
        example=search(134683853,168,drop=1,exhaust=True)
        self.assertEqual(example['completed_batches'],168)
        self.assertEqual((example['gauss_iterations'],
                          example['rows'],example['point_visits']),(739,523,693))

    def test_zero_and_intra_batch_budgets(self):
        for n in (117449,134683853):
            zero=search(n,0,drop=1)
            self.assertEqual((zero['started_batches'],zero['remaining']),(0,n))
            partial=search(n,100,drop=2,max_events=1,exhaust=True)
            self.assertEqual(partial['rows']+partial['point_visits'],1)
            self.assertEqual(partial['started_batches'],1)
            self.assertGreater(partial['unfinished_batches'],0)
        self.assertEqual(search(31**2,0)['status'],'square')
