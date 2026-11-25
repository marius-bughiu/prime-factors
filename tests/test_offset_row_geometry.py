"""Check the forced projective lifts and the disjoint adaptive lattice cover."""

from collections import Counter
from itertools import product
from math import gcd, isqrt, prod
import unittest

from experiments.offset_lattice_batches import search as ordinary_search
from experiments.offset_prime_power_slopes import local_directions
from experiments.offset_row_geometry import lifted_directions, schedule, search


class RowGeometryTests(unittest.TestCase):
    def test_label_union_equals_the_prime_square_mask(self):
        for n,p in product((19,29,31,71),(3,5,7)):
            t = isqrt(n)
            entries = lifted_directions(n,t,p,Counter())
            full = local_directions(n,t,p,2)
            q = p*p
            for j,k in product(range(q),repeat=2):
                if j%p==0 and k%p==0:
                    continue
                expected = any((b*j-a*k)%q==0 for a,b in full)
                lines = [(m,a,b) for m,a,b in entries if (b*j-a*k)%m==0]
                self.assertEqual(len(lines),int(expected))

    def test_exact_leaf_count_and_target_index(self):
        retained = (3,5,7,11)
        n = 117449
        t = isqrt(n)
        for reserve in range(5):
            masks = {p:lifted_directions(n,t,p,Counter()) for p in retained}
            leaves, generate, _ = schedule(retained,masks,reserve,Counter())
            realized = list(generate())
            self.assertEqual(len(realized),leaves)
            for labels,unused in realized:
                self.assertGreaterEqual(prod(q for q,_,_ in labels),prod(retained))
                self.assertEqual(len(labels)+len(unused),len(retained))
            # Every primitive exact square slot is on exactly one terminal line.
            winners = []
            for j,k in product(range(1,21),repeat=2):
                disc = (j+2*t*k)**2-4*n*k*k
                if gcd(j,k)==1 and disc>=0 and isqrt(disc)**2==disc:
                    count = sum(all((j*b-k*a)%q==0 for q,a,b in labels) for labels,_ in realized)
                    self.assertEqual(count,1)
                    winners.append((j,k))
            self.assertEqual(winners,[(17,12)])

    def test_complete_runs_and_partial_budgets(self):
        for n in (117449,134683853,3376036549):
            old = ordinary_search(n,1<<17,drop=2,exhaust=True)
            for reserve in (0,2,4):
                actual = search(n,1<<17,drop=2,reserve_size=reserve,exhaust=True)
                self.assertEqual(actual['proper_hits'],old['proper_hits'])
                self.assertEqual(actual['unfinished_batches'],0)
                self.assertEqual({actual['factor'],actual['remaining']},{old['factor'],old['remaining']})
                self.assertLessEqual(actual['total_batches'],old['total_batches'])
        self.assertEqual(search(9,0)['factor'],3)
        empty = search(117449,0)
        self.assertEqual(empty['started_batches'],0)
        partial = search(117449,1,max_events=1,exhaust=True)
        self.assertEqual(partial['rows']+partial['point_visits'],1)
        self.assertGreater(partial['unfinished_batches'],0)


if __name__ == '__main__':
    unittest.main()
