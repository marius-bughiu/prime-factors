"""Check the local directions, rational reconstruction, and bounded schedule independently."""

import unittest
from itertools import product
from math import gcd, isqrt, prod

from experiments.offset_crt_reconstruction import WHEEL, local_slopes, reconstruct, search


class OffsetCRTTests(unittest.TestCase):
    def test_local_directions_from_square_values(self):
        for p in (5,7,11,17):
            squares = {d*d % p for d in range(p)}
            for n in range(1,p):
                for t in range(p):
                    expected = tuple(r for r in range(p) if ((r+2*t)**2-4*n)%p in squares)+(None,)
                    self.assertEqual(local_slopes(p,n,t), expected)

    def test_all_projective_tuples_reconstruct_exactly_the_box_points(self):
        primes = (5,7,11)
        j_limit, k_limit = 12, 15
        self.assertGreater(prod(primes),2*j_limit*k_limit)
        covered = set()
        for slopes in product(*(tuple(range(p))+(None,) for p in primes)):
            pair, _ = reconstruct(primes,slopes,j_limit,k_limit)
            if pair is None:
                continue
            j,k = pair
            self.assertEqual(tuple(None if k%p==0 else j*pow(k,-1,p)%p for p in primes),slopes)
            self.assertNotIn(pair,covered)
            covered.add(pair)
        expected = {(j,k) for j in range(1,j_limit+1) for k in range(1,k_limit+1) if gcd(j,k)==1}
        self.assertEqual(covered,expected)

    def test_two_infinity_components_on_a_winning_slot(self):
        run = search(134683853,4536,exhaust=True)
        self.assertEqual((run['factor'],run['remaining'],run['first_hit']), (8231,16363,[44,35]))
        self.assertEqual((run['raw_slots'], run['total_tuples'], run['visited_tuples'], run['unchecked_tuples']),
                         (7837,4536,4536,0))
        self.assertEqual((run['convergents'],run['reconstructed'],run['square_tests'],run['proper_hits']),
                         (19791,157,156,1))
        stopped = search(134683853,1)
        self.assertEqual((stopped['status'],stopped['remaining'],stopped['unchecked_tuples']),
                         ('partial',134683853,4535))

    def test_fixed_wheel_and_shortcuts(self):
        self.assertEqual((len(WHEEL),WHEEL[0],WHEEL[-1]),(130,5,743))
        self.assertGreater(3*prod(WHEEL),8*2**1024+6*2**513)
        self.assertLess(prod((p+3)//2 for p in WHEEL),2**901)
        self.assertEqual(search(5*29,0)['factor'],5)
        self.assertEqual(search(31**2,0)['status'],'square')
        m = 134683853
        unstarted = search(m,0)
        self.assertEqual(unstarted['visited_tuples'],0)
        self.assertEqual(unstarted['unchecked_tuples'],unstarted['total_tuples'])
