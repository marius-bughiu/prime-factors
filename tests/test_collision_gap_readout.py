import unittest
from math import gcd, isqrt

from experiments.collision_gap_readout import common_gap, difference_tree, factor_from_gap, range_gcd
from experiments.sum_signature_join import search, witnessed_search


class CollisionGapReadoutTests(unittest.TestCase):
    def test_bucket_subranges_match_all_consecutive_differences(self):
        for values in ([], [9], [4, 10], [1, 7, 19, 37, 55, 85]):
            differences = [b-a for a,b in zip(values, values[1:])]
            tree, size = difference_tree(values)
            for start in range(len(differences)+1):
                for stop in range(start, len(differences)+1):
                    self.assertEqual(range_gcd(tree,size,start,stop), gcd(*differences[start:stop]))
        buckets = {'a': [2, 8, 20, 26], 'b': [5, 11, 17, 35, 41]}
        ranges = [('a', 0, 1, 4), ('b', 9, 1, 3), ('a', 48, 0, 4), ('b', -9, 4, 5)]
        sums = [offset+x for k,offset,begin,end in ranges for x in buckets[k][begin:end]]
        for anchor in sums:
            value, queries, entries = common_gap(anchor,buckets,ranges)
            self.assertEqual(value, gcd(*(v-anchor for v in sums)))
            self.assertEqual(queries, 3)
            self.assertEqual(entries, 16)

    def test_fixed_base_coincident_powers_and_equal_order(self):
        n = 49998072529
        run = witnessed_search(n, [1,3], 65536, 3)
        self.assertEqual((run['outcome'], run['factors']), ('gap_order_gcd', ['167329','298801']))
        self.assertEqual(run['work']['signature_matches'], 12)
        self.assertEqual([p['gcd'] for p in run['probes']], [str(n),'1'])
        self.assertEqual(run['work']['collision_gap']['gap'], '840')
        equal = search(220254000931, bases=(3,), incremental=True, gap_trial_cap=3)
        self.assertEqual((equal['outcome'], equal['factors']), ('common_order_sum', ['451441','487891']))
        note = equal['work']['collision_gap']
        self.assertEqual((equal['work']['signature_matches'], note['order'], note['candidate']),
                         (11, '270', '939332'))
        self.assertEqual(note['square_tests'], 1)

    def test_sixteen_false_matches_and_gap_trial_cap(self):
        n, g = 16000030340009399, 8392506781771267
        short = witnessed_search(n, [g], 1024, 0, 16)
        work = short['work']
        self.assertEqual((short['outcome'], short['factors']), ('gap_budget', []))
        self.assertEqual((work['signature_matches'],work['square_tests']), (5763,16))
        self.assertEqual(work['collision_gap']['remaining'], '60')
        self.assertEqual(len(set(work['sampled_sums'])),16)
        for s in map(int,work['sampled_sums']):
            self.assertEqual(pow(g,n+1-s,n),1)
            disc = s*s-4*n
            self.assertNotEqual(isqrt(disc)**2,disc)
        run = witnessed_search(n, [g], 1024, 2, 16)
        self.assertEqual((run['outcome'],run['factors']), ('gap_order_gcd',['100000039','160000241']))
        self.assertEqual(run['work']['sampled_sums'], work['sampled_sums'])
        note = run['work']['collision_gap']
        self.assertEqual((note['gap'],note['sample_gap'],note['trial_divisions']), ('60','92820',2))

    def test_validation_and_preflight_exits(self):
        status, factor, detail = factor_from_gap(220254000931, 3, 938625, 995561,
                                                 977132, 973352, 3, common_multiple=540)
        self.assertEqual((status,factor,detail['class_modulus']), ('common_order_sum',451441,'72900'))
        for gap in (0, 539, 1):
            with self.assertRaises(ValueError):
                factor_from_gap(220254000931, 3, 938625, 995561, 977132, 973352, 3, common_multiple=gap)
        none = witnessed_search(220254000931,[1,3],1,0)
        self.assertEqual((none['outcome'],none['work']), ('no_witness_within_cap',{}))
        for n,g,expected in [(77,7,'7'),(341,3,'11')]:
            split = witnessed_search(n,[g],1,0)
            self.assertEqual(split['outcome'],'preflight_gcd')
            self.assertIn(expected, split['factors'])
            self.assertEqual(split['work'],{})
            self.assertEqual(split['probes'][0]['fermat'] is None, g==7)
        capped = witnessed_search(49998072529,[3],1,3)
        self.assertEqual(capped['outcome'],'half_list_limit')
        self.assertEqual(capped['work']['modular_powers'],0)
