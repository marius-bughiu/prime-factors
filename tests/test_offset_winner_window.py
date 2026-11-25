import unittest
from math import isqrt

from experiments.offset_winner_window import bounds, census, coordinate_range, search


class WinnerWindowTests(unittest.TestCase):
    def test_exact_loop_boundaries(self):
        for lower in (9, 10, 13):
            for t in (lower, lower+1, 2*lower):
                for last in (5, 20, 51):
                    for v in range(1, isqrt(last)+1):
                        expected = [s for s in range(v, last+1) if
                                    s*v <= last and lower*(s-1) < t*v]
                        self.assertEqual(list(coordinate_range(t, lower, last, v)), expected)

    def test_required_endpoint_and_budget(self):
        row = search(117449, 1000)
        self.assertTrue(row['exhaustive'])
        self.assertEqual(row['hits'], [dict(j=17, k=12, d=1, factor=257)])
        self.assertLessEqual(row['visited_pairs'], row['coordinate_visits_upper'])
        self.assertTrue(search(117449, row['visited_pairs'])['exhaustive'])
        partial = search(117449, row['visited_pairs']-1)
        self.assertFalse(partial['exhaustive'])
        self.assertIsNotNone(partial['next_coordinate'])
        self.assertEqual(search(117449, 0)['visited_pairs'], 0)
        self.assertEqual(search(117449, 0)['remaining'], 117449)

    def test_balanced_primes_of_unequal_width_and_two_winners(self):
        row = search(1891, 1000, equal_width=False)
        self.assertEqual(row['L'], 31)
        self.assertEqual([(hit['j'], hit['k']) for hit in row['hits']], [(6, 1), (7, 6)])
        self.assertEqual(row['factor']*row['remaining'], 1891)

    def test_upper_prime_cap_changes_lower_endpoint(self):
        n = 127*113
        self.assertGreater(bounds(n)['L'], 64)
        self.assertLessEqual(bounds(n)['L'], 113)
        self.assertEqual(census(7)['unique_hits'], 81)

    def test_square_input_is_a_proper_split_without_a_prime_claim(self):
        row = search(81, 0)
        self.assertEqual((row['factor'], row['remaining'], row['square_tests']), (9, 9, 0))
