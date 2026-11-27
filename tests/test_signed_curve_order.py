from itertools import combinations
import unittest

from experiments.signed_curve_order import (
    POLICIES, cheapest_eligible_line, cover_check, eligible, individually, predict, search,
)
from experiments.three_root_targets import menu


class SignedCurveScheduleTests(unittest.TestCase):
    def test_cheapest_certifying_subset(self):
        cover_check()
        costs = {1: 18, 2: 14, 3: 9, 4: 6, 5: 6, 6: 7, 7: 1}
        result = cheapest_eligible_line(costs)
        self.assertEqual(result, (3, 4, 7))
        for size in range(8):
            for choice in combinations(costs, size):
                if all(any(bin(v & row).count("1") % 2 == 0 for v in choice)
                       for row in range(8)):
                    self.assertLessEqual(sum(costs[k] for k in result),
                                         sum(costs[k] for k in choice))
        self.assertEqual(cheapest_eligible_line({k: 1 for k in range(1, 8)}), (1, 2, 3))

    def test_separate_curve_replay_and_cap(self):
        for p, q in ((5, 7), (7, 13), (5, 29), (11, 59), (43, 47)):
            n = p*q
            oracle = individually(n)
            self.assertEqual(set(oracle), set(map(str, eligible(n))))
            self.assertEqual(search(n, "original")["targets"], menu(n, "signed"))
            for policy in POLICIES:
                with self.subTest(n=n, policy=policy):
                    found = search(n, policy)
                    self.assertIn(int(found["hit"]["factor"]), (p, q))
                    self.assertEqual(predict(found["order"], oracle, policy == "round_robin"),
                                     found["blocks"])
                    cap = found["blocks"]-1
                    prefix = search(n, policy, cap)
                    self.assertEqual(prefix["blocks"], cap)
                    self.assertIsNone(prefix["hit"])
