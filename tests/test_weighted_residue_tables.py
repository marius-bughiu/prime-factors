from itertools import combinations
from math import gcd
import unittest

from experiments.gap_coverage import primes_through
from experiments.weighted_residue_tables import Wheel, census
from experiments.weighted_stride_search import search
from experiments.weighted_windows import weighted_window


class WeightedResidueTableTests(unittest.TestCase):
    def test_lane_minima_count_literal_public_images_and_endpoints(self):
        wheel = Wheel((5,13))
        n = 61*113
        for a, b, start, step in [(2,1,93,4), (13,7,1584,24), (5,13,70,2)]:
            admissible = {(a*x+b*n*pow(x,-1,65)) % 65 for x in range(65) if gcd(x,65)==1}
            for length in (0, 1, 19, 65, 66, 130, 512):
                counts = [0]*65
                for i in range(length):
                    if (start+step*i)%65 in admissible:
                        counts[i%65] += 1
                for m in (1,3,7):
                    expected = sum((c+m-1)//m for c in counts)
                    self.assertEqual(wheel.lane_records(a,b,n,step,start,length,m),expected)

    def test_phase_cover_of_real_products(self):
        wheel = Wheel((5,13))
        primes = [p for p in primes_through(50) if gcd(p,6*65)==1]
        for p,q in combinations(primes,2):
            if q>2*p:
                continue
            n = p*q
            for b in range(1,9):
                for a in range(b,2*b+1):
                    if gcd(a,b)>1:
                        continue
                    low, hi = weighted_window(n,8,a,b)
                    trace, public = a*p+b*q, a+b*n
                    step = gcd(24,2*public)
                    first = low+(public-low)%step
                    if not first<=trace<=hi:
                        continue
                    u = (trace-first)//step
                    self.assertTrue(any((u+j)%65 in wheel.allowed for j in wheel.phases(a,b,n,step,first)))
        # At a genuine trace in this one-site Farey window, only the second phase works.
        phases = wheel.phases(13,7,61*113,24,1584)
        self.assertEqual(weighted_window(61*113,8,13,7), (1584,1584))
        self.assertEqual(13*61+7*113, 1584)
        self.assertEqual([j in wheel.allowed for j in phases], [False,True])

    def test_sparse_record_count_and_period_guards(self):
        wheel = Wheel((5,13))
        self.assertEqual(wheel.holes,[1,2])
        for phase in (0,1,14,64):
            for length in (0,1,2,60,65,74,299):
                for span in (65,195):
                    blocks = {i//span for i in range(phase,phase+length) if i%65 in wheel.allowed}
                    self.assertEqual(wheel.sparse_records(span,length,phase),len(blocks))
        tiny = census(61*113,8,44,wheel,65,max_slopes=2)
        self.assertFalse(tiny['complete'])
        for invalid in [(5,5),(5,0),(-5,7),(5,49),(999983,)]:
            with self.assertRaises(ValueError):
                Wheel(invalid)

    def test_sparse_search_counts_and_limits(self):
        n = 1900014700027
        wheel = Wheel([5,13])
        r = search(n,8,71,1000,wheel_primes=wheel.primes)
        self.assertIn(r['factor'],(1000003,1900009))
        self.assertTrue(r['schedule_complete'])
        work = r['work']
        self.assertEqual((work['baby_span'],work['babies'],work['order_positions']),(65,44,64))
        c = census(n,8,71,wheel,65,max_slopes=1000)
        self.assertEqual((work['giants'],work['phase_schedules']),(c['sparse_giants'],c['phase_schedules']))
        self.assertEqual(work['evaluations'],65)
        self.assertEqual(work['retained_evaluations'],44)
        for cap, kwargs in [('span_limit', {'max_span':64}),('baby_limit', {'max_babies':32}),
                            ('giant_limit', {'max_giants':0}),('slope_limit', {'max_slopes':0})]:
            settings = dict(max_giants=1000,wheel_primes=[5,13])
            settings.update(kwargs)
            run = search(n,8,71,**settings)
            self.assertEqual((run['factor'],run['limit'],run['schedule_complete']),(None,cap,False))
        self.assertEqual(search(n,8,20,1000,wheel_primes=[5,13])['limit'],'wheel_capacity')
        self.assertEqual(search(35,8,70,1000,wheel_primes=[5])['factor'],5)

    def test_global_equalities_check_both_padding_bounds_and_every_origin(self):
        padded = [(1,1,1,12,1,1,2), (2,1,1,11,1,0,1)]
        def emit(*args):
            return padded, None
        # For N=35, the valid discriminant is at trace 12. The first two
        # records put it just below or just above their permitted indices.
        r = search(35,1,2,10,stride=1,record_builder=emit)
        self.assertEqual((r['factor'],r['work']['equality_checks']),(None,0))
        padded.append((2,1,1,11,1,1,2))
        r = search(35,1,2,10,stride=1,record_builder=emit)
        self.assertEqual((r['factor'],r['work']['equality_checks']),(5,1))
