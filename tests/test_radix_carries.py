import unittest

from experiments.radix_carries import nearest, search


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
