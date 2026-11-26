from math import gcd
import unittest

from experiments.block_exclusion_certificate import generate, verify


class BlockExclusionCertificateTests(unittest.TestCase):
    def test_checked_lean_example(self):
        offsets, nodes = [1,5,7,11], [24,36,48]
        result = generate(16003, offsets, nodes)
        self.assertEqual(result['status'], 'certified')
        self.assertEqual(result['u'], [8172,14696,12609])
        self.assertEqual(result['v'], [9710,100,1231,3394])
        self.assertEqual(result['work']['scalar_inversions'], 1)
        self.assertEqual(result['work']['batch_multiplications'], 3*(len(nodes)-1))
        self.assertTrue(verify(16003, offsets, nodes, result['u'], result['v']))
        self.assertFalse(verify(16003, offsets, nodes, result['u']+[1], result['v']))

    def test_repeated_nodes_and_noninvertible_differences(self):
        offsets, nodes = [1,4,1], [0,3,3,15]
        result = generate(15, offsets, nodes)
        self.assertTrue(verify(15, offsets, nodes, result['u'], result['v']))
        self.assertLessEqual(len(result['u']), len(nodes))
        self.assertLessEqual(len(result['v']), len(offsets))
        self.assertEqual(result['work']['synthetic_divisions'], len(nodes))
        # U*A=1 holds at the point 0, but fails modulo X².
        self.assertFalse(verify(15, [1], [0,0], [1], []))

    def test_small_rectangles_against_direct_gcds(self):
        lists = ([], [0], [1], [1,2], [0,4], [2,2,7], [0,3,15])
        for n in (6,9,15,23,25,35,49,77):
            for offsets in lists:
                for nodes in lists:
                    with self.subTest(n=n, offsets=offsets, nodes=nodes):
                        result = generate(n, offsets, nodes)
                        gcds = [gcd(a+b,n) for a in offsets for b in nodes]
                        if any(1 < d < n for d in gcds):
                            expected = 'factor'
                        elif n in gcds:
                            expected = 'multiple_of_n'
                        else:
                            expected = 'certified'
                        self.assertEqual(result['status'], expected)
                        if expected == 'certified':
                            self.assertTrue(verify(n, offsets, nodes, result['u'], result['v']))
                            self.assertEqual(result['work']['scalar_inversions'],
                                             int(bool(offsets and nodes)))
                        else:
                            cell = result['collision']
                            candidate = offsets[cell['offset_index']]+nodes[cell['node_index']]
                            self.assertEqual(cell['candidate'], candidate)
                            self.assertEqual(gcd(candidate,n), result['factor'] or n)
                            self.assertIsNone(result['u'])
                            self.assertEqual(result['work']['scalar_inversions'], 0)

    def test_finds_proper_collision_after_whole_modulus(self):
        result = generate(15, [0,3], [15])
        self.assertEqual(result['factor'], 3)
        self.assertEqual(result['collision']['candidate'], 18)
        self.assertEqual(result['work']['candidate_gcds'], 2)

    def test_invalid_input(self):
        for arguments in ((1, [], []), (77, [-1], [3]), (77, [1], [-3])):
            with self.assertRaises(ValueError):
                generate(*arguments)
