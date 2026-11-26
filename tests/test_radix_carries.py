import unittest

from experiments.radix_carries import nearest, search, search_neighbors


class RadixCarryTests(unittest.TestCase):
    def test_rounding_half_ties_in_both_directions(self):
        self.assertEqual([nearest(n, 8) for n in (-13, -12, -5, -4, 3, 4)], [-2, -1, -1, 0, 0, 1])

    def test_signed_correction_recovers_divisor(self):
        self.assertIsNone(search(143, 0, 0)[0])
        divisor, work = search(143, 4, 4)
        self.assertEqual(divisor, 13)
        self.assertEqual(work["hit"], dict(exponent=3, high=-1, low=2))
        self.assertEqual(work["square_hits"], 1)

    def test_perfect_square_can_give_trivial_gcd(self):
        divisor, work = search(23, 4, 4)
        self.assertIsNone(divisor)
        self.assertGreater(work["square_hits"], 0)
        self.assertEqual(work["candidates"], work["radices"] * 81)
        self.assertIsNone(work["hit"])

    def test_neighbor_scan_counts_bases_before_the_winning_base(self):
        divisor, short = search_neighbors(135137, 0, 2, 9)
        self.assertIsNone(divisor)
        self.assertEqual((short["neighbor_checks"], short["radices"]), (9, 1))
        divisor, full = search_neighbors(135137, 0, 2, 10)
        self.assertEqual(divisor, 337)
        self.assertEqual(full["hit"], {"radix": 41, "high": 0, "low": -2})
        self.assertEqual((full["neighbor_checks"], full["radices"]), (10, 2))
        self.assertEqual(search_neighbors(15, 0, 2, 1)[0], 5)  # The radix divides N+1.
