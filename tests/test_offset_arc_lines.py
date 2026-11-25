import unittest
from collections import Counter
from math import isqrt
from random import Random

from experiments.offset_arc_lines import Strip, line_roots, projection, search
from experiments.offset_tangent_cover import arc_hits, cube_root, epochs, search as tangent_search, shifted_bounds


class OffsetArcTests(unittest.TestCase):
    def test_integer_points_are_on_the_reported_levels(self):
        rng = Random(34617)
        for _ in range(300):
            width, den = rng.randrange(1,24), rng.randrange(1,30)
            low = rng.randrange(-80,81)
            strip = Strip(width,rng.randrange(-80,81),den,low,low+rng.randrange(31))
            p,q,first,last,lower = projection(strip,Counter())
            self.assertLessEqual(lower,max(0,last-first+1))
            for i in range(width+1):
                for y in range(-((-(strip.slope*i+strip.low))//den),(strip.slope*i+strip.high)//den+1):
                    self.assertLessEqual(first,q*y-p*i)
                    self.assertLessEqual(q*y-p*i,last)

    def test_compressed_discriminant_and_degenerate_lines(self):
        # Include slopes equal to each asymptote, repeated roots and nonintegral intersections.
        for S,step,P in ((10,1,40),(5,2,25),(11,3,29)):
            for q in (1,3):
                for g in range(-3*q,3*q+1):
                    for f in range(-19,20):
                        found = {i for i in line_roots(S,step,P,f,g,q,Counter()) if -9<=i<=9}
                        expected = {i for i in range(-9,10) if (f+g*i)**2 == q*q*((S+step*i)**2-P)}
                        self.assertEqual(found,expected)

    def test_tangent_epoch_cover_matches_every_signed_root(self):
        for product,trace,step,modulus in ((24,5,1,48),(120,11,3,96),(756,28,2,180)):
            for residue,slope in ((1,3),(modulus-1,-7),(0,0)):
                found = set()
                covered = []
                for left,stop,chunk in epochs(trace,step,100,product,modulus,Counter()):
                    for begin in range(left,stop,chunk):
                        size = min(stop-begin,chunk)
                        covered.extend(range(begin,begin+size))
                        work = Counter()
                        for i,z in arc_hits(trace+step*begin,step,size-1,product,
                                            (residue+slope*begin)%modulus,slope,modulus,work):
                            found.add((begin+i,z))
                        self.assertLessEqual(work['line_equations'],2)
                self.assertEqual(covered,list(range(100)))
                expected = set()
                for i in range(100):
                    delta = (trace+step*i)**2-product
                    root = isqrt(delta)
                    if root*root == delta:
                        expected.update((i,z) for z in {root,-root} if (z-residue-slope*i)%modulus == 0)
                self.assertEqual(found,expected)

    def test_cube_threshold_at_large_perfect_powers(self):
        for r in (1,2,10,2**257+39):
            self.assertEqual(cube_root(r**3-1),r-1)
            self.assertEqual(cube_root(r**3),r)
            self.assertEqual(cube_root(r**3+1),r)

    def test_endpoint_and_exhaustion_budgets(self):
        for hybrid in (True,False):
            opts = dict(max_vectors=100,all_vectors=True,hybrid=hybrid)
            done = search(117449,8,max_tests=1000,**opts)
            self.assertEqual(done['hits'],[[17,12,'257','457']])
            self.assertEqual(done['remaining_tests'],0)
            capped = search(117449,8,max_tests=0,**opts)
            self.assertEqual(capped['remaining_tests'],done['scheduled'])
            self.assertFalse(capped['hits'])
        capped = tangent_search(117449,max_vectors=1,max_arcs=0,all_vectors=True)
        self.assertFalse(capped['schedule_exhausted'])
        self.assertEqual(capped['planned_arcs'],capped['remaining_arcs'])
        self.assertEqual(capped['visited_arcs'],0)

    def test_previous_integer_base_on_product_only_two_above_a_square(self):
        n = 25283
        self.assertEqual(n-isqrt(n)**2,2)
        box = shifted_bounds(n)
        self.assertEqual((box['T'],box['h'],box['J'],box['K']),(158,319,20,10))
        run = tangent_search(n,max_vectors=100,max_arcs=1000,all_vectors=True,
                             lift_cap=1,trace_units=False,shifted_base=True)
        self.assertEqual(run['hits'],[[8,1,'131','193']])
        self.assertTrue(run['schedule_exhausted'])
        self.assertEqual(run['remaining_arcs'],0)
