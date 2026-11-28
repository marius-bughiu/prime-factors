import unittest

from experiments.toy_period_sum_order import check_direct, retrospective_ranks


class PeriodSumOrderTests(unittest.TestCase):
    def test_final_block_and_both_extremes(self):
        for n, lo, hi, p, q, expected in [
            (7253249, 5387, 5589, 2053, 3533, (14, 9)),
            (7688801, 5546, 5802, 2063, 3727, (17, 19)),
            (6296551, 5019, 5122, 2053, 3067, (8, 8)),
        ]:
            with self.subTest(n=n):
                ranks = retrospective_ranks(n, lo, hi, p + q)
                self.assertEqual((ranks.ascending, ranks.prioritized), expected)
                check_direct(n, lo, hi, (p, q), ranks)
        clipped = retrospective_ranks(6296551, 5019, 5122, 5120)
        self.assertGreater(clipped.omitted_priority, 0)
