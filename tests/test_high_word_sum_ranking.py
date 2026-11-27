import unittest

from experiments.high_word_sum_ranking import propose, row_count, search


class HighWordSumRankingTests(unittest.TestCase):
    def test_selected_row_and_final_check_use_distinct_information(self):
        for n in (135069793, 135069794):
            self.assertEqual(propose(14, n >> 14)['counts'], [17, 34])
        factor, work = search(135069793, 14)
        self.assertEqual((factor, work['midpoint'], work['square_tests']), (11467, 11623, 1))
        factor, work = search(134375149, 14)
        self.assertIsNone(factor)
        self.assertEqual((work['setup_roots'], work['square_tests']), (4, 0))

    def test_populated_integer_rows_can_have_different_prime_populations(self):
        base, word = 16384, 8197
        lower = base * word
        upper = lower + base - 1
        self.assertEqual([row_count(base, lower, upper, u)[0] for u in (11589, 11590, 11591)],
                         [36, 29, 20])
