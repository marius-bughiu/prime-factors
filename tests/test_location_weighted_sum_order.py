import unittest

from experiments.location_weighted_sum_order import census, merge_keys, replay


class LocationWeightedOrderTests(unittest.TestCase):
    def test_merge_breaks_priority_ties_by_smaller_sum(self):
        # Opposite group membership on the two tied priorities.
        self.assertEqual(merge_keys([(12, 31), (80, 47)], [(12, 29), (80, 49)]),
                         ([29, 31, 47, 49], 3))
        self.assertEqual(merge_keys([], [(7, 15)]), ([15], 0))

    def test_complete_nine_bit_census_and_costs(self):
        row = census(9)
        all_pairs, square = row['groups']['all'], row['groups']['square_unit']
        self.assertEqual((all_pairs['pairs'], square['pairs']), (543, 263))
        self.assertEqual([all_pairs[name] for name in ('ascending', 'global', 'weighted', 'offset')],
                         [749, 738, 735, 738])
        self.assertEqual([square[name] for name in ('ascending', 'global', 'weighted', 'offset')],
                         [350, 339, 336, 339])
        self.assertEqual(all_pairs['offset_cost_changes'], 5)
        self.assertEqual((row['overhead']['sort_comparisons'], row['overhead']['merge_comparisons'],
                          row['overhead']['merge_comparisons_through_hit']), (349, 183, 157))

    def test_actual_losses_against_each_reference(self):
        ordinary = replay(134599, 9)
        self.assertEqual(ordinary['factors'], (281, 479))
        self.assertEqual(ordinary['tests'], {'ascending': 3, 'global': 4, 'weighted': 4, 'offset': 4})
        favored = replay(132289, 9)
        self.assertEqual(favored['factors'], (263, 503))
        self.assertEqual(favored['tests'], {'ascending': 4, 'global': 2, 'weighted': 3, 'offset': 3})

    def test_bounds_and_nonsquare_product(self):
        with self.assertRaises(ValueError):
            replay(134599, 15)
        with self.assertRaises(ValueError):
            replay(134599, 8)
        result = replay(7*5, 3)
        self.assertEqual(set(result['tests'].values()), {1})
        self.assertEqual(result['score_discriminants'], 0)
        self.assertEqual(result['sort_comparisons'], 0)


if __name__ == '__main__':
    unittest.main()
