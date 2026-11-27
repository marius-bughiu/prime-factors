import unittest

from experiments.geometry_weight_menu import TABLE, census, direct


class GeometryWeightMenuTests(unittest.TestCase):
    def test_allocations(self):
        expected = {
            1: ((7,5,9), (13,11,6)),
            5: ((7,5,8), (9,7,7)),
            7: ((7,5,7), (11,7,8)),
            11: ((3,2,7), (11,7,8)),
        }
        for r, arms in TABLE.items():
            self.assertEqual(arms, expected[r%12])
            self.assertEqual(sum(h for _,_,h in arms), 15)

    def test_prime_partner_intervals_replay_all_square_tests(self):
        row = direct(12)
        row.pop('direct_geometry')
        self.assertEqual(row, census(12))
