import unittest

from experiments.mixed_ratio_heights import census, jacobi, optimal_pair


class MixedRatioHeightTests(unittest.TestCase):
    def test_blum_heights_on_opposite_sides_of_cutoff(self):
        self.assertEqual(optimal_pair(19, 23, 2, 21), (49, 49, [(4, 9), (49, 1)]))
        self.assertEqual(optimal_pair(19, 23, 1, 208), (256, 256, [(1, 169), (256, 1)]))

    def test_least_nonresidue_beats_every_unscaled_divisor_choice(self):
        self.assertEqual(optimal_pair(23, 31, 1, 185), (555, 555, [(3, 185), (555, 1)]))
        self.assertEqual(jacobi(3, 23*31), -1)

    def test_direct_census_up_to_31(self):
        totals = census(31)
        self.assertEqual(totals['mixed_ratios']-totals['square_eligible'],
                         totals['blum_ratios']-totals['blum_eligible'])
        self.assertGreater(totals['blum_ratios'], totals['blum_eligible'])
        self.assertGreater(totals['square_eligible'], totals['blum_eligible'])
