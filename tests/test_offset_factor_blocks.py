import unittest
from math import gcd, isqrt

from experiments.offset_factor_blocks import determinant_span, endpoint_basis, search, select_block


def exhaustive(n, lower, upper, shifted, parity):
    """Independently enumerate the sharp norm inequality on each integral trial d."""
    t = isqrt(n)-int(shifted)
    h = n-t*t
    limit = isqrt(4*h//3)
    sharp = set()
    rounded = {}
    for d in range(lower, upper+1):
        for v in range(1, d+1):
            # R >= H*v² gives this bound directly, including every real-short trial.
            if 3*(h*v*v)**2 > 4*d*d*h:
                break
            for s in range(v,2*v+1):
                if gcd(s,v) != 1:
                    continue
                value = (d*s-t*v)**2+h*v*v
                if 3*value*value <= 4*d*d*h:
                    sharp.add((s,v))
                if value <= d*(limit-((limit-s-v)%2 if parity else 0)):
                    rounded.setdefault((s,v),[]).append(d)
    return sharp, rounded


class FactorBlockTests(unittest.TestCase):
    def test_whole_blocks_against_trial_by_trial_enumeration(self):
        for n in (1891,2501,9017,34387,117449,122821,126187):
            for shifted in (False,True):
                h = n-(isqrt(n)-int(shifted))**2
                size = isqrt(h)//4+1
                lower = isqrt((n-1)//2)+1
                for start in range(lower,isqrt(n)+1,size):
                    end = min(isqrt(n),start+size-1)
                    for parity in (False,True):
                        selected = select_block(n,start,end,shifted=shifted,parity=parity)
                        sharp, rounded = exhaustive(n,start,end,shifted,parity)
                        predicted = {(row['s'],row['v']):list(range(row['lower'],row['upper']+1))
                                     for row in selected['charts']}
                        self.assertEqual(predicted,rounded)
                        self.assertTrue(sharp.issubset(selected['endpoint_directions']))
                        self.assertLessEqual(len(selected['endpoint_directions']),3)

    def test_three_directions_and_zero_dot_tie(self):
        selected = select_block(126187,257,264)
        self.assertEqual(selected['charts'],[
            dict(s=1,v=1,lower=264,upper=264),
            dict(s=3,v=2,lower=257,upper=259),
            dict(s=4,v=3,lower=259,upper=264),
        ])
        left,right,dot,_ = endpoint_basis(0,25,7)
        self.assertEqual(dot,0)
        self.assertEqual(left[0]*right[1]-left[1]*right[0],1)
        for sign in (-1,1):
            s,v = left[0]+sign*right[0],left[1]+sign*right[1]
            self.assertGreaterEqual((49*s*s+25*v*v)**2,4*49*25)

    def test_budget_and_recovery(self):
        complete = search(122821,max_blocks=100,max_tests=1000)
        self.assertTrue(complete['schedule_exhausted'])
        self.assertEqual(complete['hits'],[[32,1,'263','467'],[35,12,'263','467']])
        skipped = search(122821,max_blocks=3,start_block=2,max_tests=0)
        self.assertEqual((skipped['visited_blocks'],skipped['tested_positions'],skipped['hits']),(3,0,[]))
        stage = search(117449,max_blocks=100,max_tests=0,shifted=False)
        self.assertEqual(stage['unvisited_blocks'],0)
        self.assertEqual(stage['unscanned_charts'],2)
        self.assertFalse(stage['schedule_exhausted'])
        exterior = search(122821,max_blocks=1,start_block=1,max_tests=1000)
        self.assertEqual(exterior['hits'],[])
        self.assertEqual(exterior['tested_positions'],1)

    def test_interval_preconditions(self):
        for bounds in ((10,9),(0,3),(256,264),(350,351)):
            with self.assertRaises(ValueError):
                select_block(122821,*bounds)
        for n in (4,9,20):
            with self.assertRaises(ValueError):
                search(n,max_blocks=0)
        with self.assertRaises(ValueError):
            search(122821,max_blocks=1,start_block=13)

    def test_guide_interval_is_strict_at_both_ends(self):
        # With T=3, H=1 and J=1, d=2 and d=5 give equality.
        self.assertEqual(determinant_span(10,3,1,1,1,1),(3,4))
        for n in (1891,2501,117449,122821):
            for t in (isqrt(n),isqrt(n)-1):
                h = n-t*t
                height = isqrt(4*h//3)
                for s,v in ((1,1),(4,3),(3,2),(2,1)):
                    span = determinant_span(n,t,h,height,s,v)
                    for d in range(t//2, t+2):
                        passes = height*((d*s-t*v)**2+h*v*v) < d*h
                        self.assertEqual(passes,span is not None and span[0]<=d<=span[1])

    def test_coalescing_preserves_exact_coverage_and_hits(self):
        fields = ('visited_blocks','unvisited_blocks','empty_blocks','chart_intervals','unique_charts',
                  'untested_intervals','tested_positions','scanned_charts','hits','schedule_exhausted')
        for n in (2501,34387,117449,122821,126187):
            for shifted in (False,True):
                for parity in (False,True):
                    for start,limit in ((0,100),(1,5),(2,2)):
                        options = dict(start_block=start,max_blocks=limit,shifted=shifted,
                                       parity=parity,max_tests=1000)
                        ordinary = search(n,**options)
                        grouped = search(n,coalesce=True,**options)
                        for field in fields:
                            self.assertEqual(ordinary[field],grouped[field],(n,options,field))
                        if not grouped['untested_intervals']:
                            self.assertEqual((grouped['untested_chart_positions_lower'],
                                              grouped['untested_chart_positions_upper']),(0,0))
                        self.assertEqual(grouped['visited_blocks'],
                                         grouped['endpoint_reductions']+grouped['coalesced_blocks'])

    def test_independent_reduction_and_coverage_budgets(self):
        n = 117449
        none = search(n,max_blocks=3,max_tests=1000,coalesce=True,max_reductions=0)
        self.assertEqual((none['endpoint_reductions'],none['visited_blocks'],none['guide_tests'],
                          none['hits']),(0,0,0,[]))
        grouped = search(n,start_block=4,max_blocks=5,max_tests=1000,shifted=False,
                         coalesce=True,max_reductions=1)
        self.assertEqual((grouped['endpoint_reductions'],grouped['visited_blocks'],
                          grouped['guide_regions'],grouped['coalesced_blocks']),(1,5,1,4))
        self.assertGreaterEqual(grouped['guide_interval_roots'],1)
        self.assertEqual(grouped['hits'],[])
        self.assertEqual(grouped['unvisited_prefix_blocks']+grouped['unvisited_suffix_blocks'],
                         grouped['unvisited_blocks'])
        # An entire 33-million-block suffix is charged to one endpoint reduction.
        tail = search(3*(1<<251)+19,max_blocks=1<<25,from_end=True,coalesce=True,max_reductions=1)
        self.assertEqual((tail['unique_charts'],tail['endpoint_reductions'],tail['visited_blocks']),
                         (1,1,1<<25))
        self.assertEqual(tail['unvisited_suffix_blocks'],0)
        self.assertEqual(tail['start_block'],tail['total_blocks']-tail['visited_blocks'])
        self.assertEqual(tail['candidate_lower'],0)  # zero position budget, chart not scanned
        limited = search(3*(1<<251)+19,max_blocks=1<<25,from_end=True,coalesce=True,
                         max_reductions=1,max_tests=3)
        self.assertGreater(limited['untested_intervals'],0)
        self.assertEqual(limited['tested_positions'],3)
        self.assertEqual(limited['untested_chart_positions_lower'],limited['candidate_lower']-3)
        self.assertEqual(limited['untested_chart_positions_upper'],limited['candidate_upper']-3)
        with self.assertRaises(ValueError):
            search(n,max_blocks=4,from_end=True,start_block=1)
        with self.assertRaises(ValueError):
            search(n,max_blocks=1,max_reductions=1)
