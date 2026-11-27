from collections import Counter
import unittest

from experiments.signed_norm_arcs import check_small, exact_points, point_scan, search
from experiments.unit_reduced_signed_arcs import verify_small


class SignedNormArcTests(unittest.TestCase):
    def test_complete_signed_point_sets(self):
        self.assertEqual(check_small(), {
            "signed_equations": 4064, "nonnegative_solutions": 1129, "wide_blocks": 4,
        })

    def test_unit_charts_preserve_all_root_classes(self):
        proof = verify_small()
        self.assertEqual(proof["domain_equations"], 7112)
        self.assertEqual(proof["semiprimes"], 190)

    def test_exact_budget_includes_last_block_and_coordinate(self):
        for method, cap_key, count_key in (
            ("arcs", "max_blocks", "blocks"), ("direct", "max_positions", "coordinate_positions"),
        ):
            full = Counter()
            expected = sorted(point_scan(24881, 2, -1, method, full))
            self.assertEqual(expected, sorted(exact_points(24881, 2, -1)))
            self.assertGreater(full[count_key], 1)
            for difference in (0, 1):
                work = Counter()
                cap = full[count_key]-difference
                actual = list(point_scan(24881, 2, -1, method, work, **{cap_key: cap}))
                self.assertEqual(work[count_key], cap)
                self.assertEqual(bool(work["capped"]), bool(difference))
                self.assertTrue(set(actual) <= set(expected))
                if difference == 0:
                    self.assertEqual(sorted(actual), expected)

    def test_same_search_certificate_inputs(self):
        n = 43*47
        direct = search(n, "direct")
        arcs = search(n, "arcs")
        self.assertTrue(arcs["complete"])
        self.assertEqual(direct["points"], arcs["points"])
        for result in (arcs, direct):
            self.assertIn(int(result["factor"]), (43, 47))
            self.assertLessEqual(result["first_work"]["coordinate_positions"],
                                 result["work"]["coordinate_positions"])
        self.assertFalse(search(n, "arcs", max_blocks=0)["complete"])
