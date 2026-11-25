import unittest
from collections import Counter
from math import gcd

from experiments.affine_radix_holdout import trial_search
from experiments.midpoint_weights import residue_pairs
from experiments.unit_factor_lane import search


class UnitFactorLaneTests(unittest.TestCase):
    def test_matches_the_single_predicted_group_on_every_small_odd_input(self):
        for n in range(3, 2001, 2):
            run = search(n)
            radix = run['radix']
            expected = [pair for pair in trial_search(n)['pairs']
                        if any(int(p) % radix == 1 for p in pair)]
            self.assertEqual(run['pairs'], expected, n)
            self.assertEqual(run['total_orbits'], residue_pairs(n, radix, Counter())[0])
            self.assertEqual(run['remaining_orbits'], run['total_orbits']-1)
            self.assertEqual(gcd(n, radix), 1)
