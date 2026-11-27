import unittest
from math import gcd
from unittest.mock import patch

from experiments.complementary_keys import norm_forms, search
from experiments.twelve_residue_collision import keys


class ComplementaryNormBranchTests(unittest.TestCase):
    @staticmethod
    def prescribed(n, samples):
        with patch('experiments.complementary_keys.Random') as random:
            random.return_value.randrange.side_effect = samples
            return search(n, len(samples), 0)

    def test_global_complement_at_different_local_branches(self):
        n = 1040279
        u, v = keys([4, 11], n)
        self.assertEqual((u, v), (1001365, 38915))
        self.assertEqual((gcd(n, u-v), gcd(n, u+v-1)), (1, n))
        self.assertEqual([gcd(n, z) for z in norm_forms(4, 11)], [1031, 1, 1009, 1, 1, 1])
        factor, work, _ = self.prescribed(n, [4, 11])
        self.assertEqual((factor, work['source'], work['norm_index']), (1031, 'complement norm', 0))
        self.assertEqual((work['norm_gcds'], work['witness']), (1, ['4', '11']))

    def test_global_middle_also_checks_self_pair(self):
        n, seed = 808057, 67493
        value, = keys([seed], n)
        self.assertEqual((2*value-1) % n, 0)
        factor, work, _ = self.prescribed(n, [seed])
        self.assertEqual((factor, work['norm_index'], work['norm_gcds']), (911, 3, 4))
        self.assertEqual(work['witness'], ['67493', '67493'])

    def test_noncolliding_pair_spends_no_norm_gcds(self):
        factor, work, _ = self.prescribed(1040279, [2, 4])
        self.assertIsNone(factor)
        self.assertEqual(work['norm_gcds'], 0)
