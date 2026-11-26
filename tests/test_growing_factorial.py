from itertools import combinations
from math import gcd
import unittest

from collections import Counter
from experiments.factorial_progressions import search as complete
from experiments.growing_factorial import grow_tables, search
from experiments.short_pascal_row import interval
from scripts.factor import primes_through


class GrowingFactorialTests(unittest.TestCase):
    def test_partial_and_centered_ranges_match_literal_wheel_candidates(self):
        primes = [p for p in primes_through(1023) if 512 <= p][::3]
        for p, q in combinations(primes, 2):
            n = p*q
            lower, upper = interval(n)
            for cap in (0, 1, (upper-lower)//2, None):
                for folded in (False, True):
                    w = 6
                    run = search(n, cap, wheel=w, folded=folded)
                    last = int(run['last'])
                    ranges = [tuple(map(int, pair)) for pair in run['ranges']]
                    candidates = [v for lo, hi in ranges for v in range(lo, hi+1)]
                    self.assertEqual(len(candidates), int(run['covered_span']))
                    self.assertEqual(candidates, sorted(set(candidates)))
                    self.assertTrue(all(lower <= v <= last for v in candidates))
                    charged = run['work'].get('batched_candidates', 0)+run['work'].get('direct_candidates', 0)
                    self.assertEqual(charged, sum(gcd(v,w)==1 for v in candidates))
                    self.assertEqual(run['factor'], p if lower <= p <= last else None)
                    if run['factor'] is None:
                        self.assertEqual(candidates, list(range(lower, last+1)))
                    elif run['outcome'] == 'prefix_gcd':
                        self.assertIn(p, candidates)

    def test_overlap_at_an_odd_block_boundary_and_hit_before_far_end(self):
        # A nonterminal degree-plus-one array has an odd number of blocks.
        n = 659065157 * (645478771983487933//659065157)
        run = search(n, None)
        self.assertEqual(run['factor'], 659065157)
        self.assertGreater(run['work']['convolutions'], 2)
        self.assertLess(int(run['covered_through']), int(run['upper']))

    def test_wheel_and_empty_budget(self):
        self.assertEqual(search(35,None)['factor'],5)
        self.assertEqual(search(143,None,wheel=143,folded=True)['factor'],11)
        self.assertIsNone(search(35,0)['factor'])

    def test_growing_tables_preserve_units_and_find_a_new_nonunit(self):
        n = 101*103
        fact, inv, recip, work = [1], [1], [], Counter()
        for limit in (7, 5, 8, 81):
            self.assertIsNone(grow_tables(limit,n,fact,inv,recip,work))
            self.assertTrue(all(a*b % n == 1 for a,b in zip(fact,inv)))
            self.assertTrue(all(j*r % n == 1 for j,r in enumerate(recip,1)))
        self.assertEqual(work['table_entries_built'],81)
        self.assertEqual(grow_tables(107,n,fact,inv,recip,work),101)

    def test_final_grid_uses_no_more_convolution_inputs_on_a_hit_or_a_miss(self):
        for n in (101*113, 521*677, 4099*5003, 32771*53993):
            for folded in (False, True):
                for cap in (31, 301, 1013, 4000, None):
                    full = complete(n,cap,wheel=6,folded=folded,equal_width=True)
                    early = search(n,cap,wheel=6,folded=folded,final_grid=True)
                    self.assertEqual(early['factor'],full['factor'])
                    self.assertLessEqual(early['work'].get('convolution_input_coefficients',0),
                                         full['work'].get('convolution_input_coefficients',0))

    def test_whole_interval_coefficient_budget_admits_an_exactly_affordable_stage(self):
        n = 645478771983487933
        for folded in (False, True):
            def run(budget):
                return search(n, None, folded=folded, final_grid=True, max_inputs=budget)
            seed = run(0)
            required = seed['work']['next_convolution_inputs']
            short = run(required-1)
            exact = run(required)
            self.assertEqual(short['ranges'], seed['ranges'])
            self.assertEqual(short['work'].get('convolution_input_coefficients', 0), 0)
            self.assertEqual(exact['work']['convolution_input_coefficients'], required)
            self.assertGreater(int(exact['covered_span']), int(seed['covered_span']))
            self.assertEqual(exact['last'], exact['upper'])
            self.assertEqual(exact['outcome'], 'convolution_limit')
            if folded:
                self.assertGreater(int(exact['ranges'][0][0]), int(exact['low']))
