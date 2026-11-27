import unittest

from experiments.intermediate_totient_rows import product_band, run_fixture, scan


class IntermediateTotientRowsTests(unittest.TestCase):
    def test_single_block_matches_all_brute_rows(self):
        for n in range(2, 65):
            for e in range(1, n+1):
                counts, _ = scan(n, 3, e, compare_raw=True)
                self.assertLessEqual(counts["blocks_clipped"], 1)
                self.assertLessEqual(counts["visited_blocks"], counts["previous_visited_blocks"])
                self.assertLessEqual(counts["endpoint_divisions"], counts["previous_endpoint_divisions"])

    def test_instants_and_first_block(self):
        for n in (3, 91, 143):
            counts, found = scan(n, 4, n, compare_raw=True)
            self.assertEqual(counts["blocks_clipped"], 0)
            self.assertEqual(counts["width_indices"], 0)
            self.assertEqual(counts["visited_blocks"], 1)
            self.assertEqual(found, {})
        with self.assertRaises(ValueError):
            scan(143, 4, 0)
        counts, found = scan(17*23, 5, 1, compare_raw=True)
        self.assertEqual(set(found), {"first_block"})
        self.assertEqual(found["first_block"]["t"], 16*22)
        self.assertEqual(counts["first_block_indices"], 32)

    def test_complementary_factor_example(self):
        result = run_fixture({"n": "102709", "factor_bits": 9})
        self.assertEqual(result["pair"], ["271", "379"])
        self.assertEqual(set(result["hits"]), {"later_intermediate", "fermat"})
        work = result["counts"]
        self.assertEqual(work["discriminant_roots"], 1)
        self.assertEqual(work["matched_total_midpoints_spent"], 1)
        self.assertEqual(work["matched_without_setup_midpoints"], 0)
        self.assertEqual(work["band_setup_roots"], 1)
        self.assertEqual(work["band_setup_divisions"], 2)
        self.assertEqual(work["fermat_midpoints"], 5)
        self.assertEqual(work["endpoint_divisions"], 2*work["blocks_clipped"])

    def test_sharp_setup_is_charged_even_when_candidate_budget_is_zero(self):
        result = run_fixture({"n": "7", "factor_bits": 3})
        self.assertEqual(result["counts"]["discriminant_roots"], 0)
        self.assertEqual(result["counts"]["matched_total_setup_roots"], 1)
        self.assertEqual(result["counts"]["matched_total_midpoints_spent"], 0)
        self.assertEqual(result["counts"]["matched_without_setup_initial_roots"], 0)

    def test_physical_endpoints_and_subset_locator(self):
        for bits in range(3, 7):
            odd = range((1 << (bits-1))+1, 1 << bits, 2)
            for p in odd:
                for q in odd:
                    low, high = product_band(p*q, bits)
                    self.assertLessEqual(low, p+q-1)
                    self.assertLess(p+q-1, high)
                    self.assertEqual((low % 2, high % 2), (1, 0))
        n = 17*23
        self.assertEqual(product_band(n, 5), (39, 40))
        counts, hits = scan(n, 5, 1, band=product_band(n, 5), compare_raw=True)
        self.assertEqual(counts["width_indices"], 1)
        self.assertEqual(hits["first_block"]["t"], 16*22)
        for n in range(16,65):
            band = product_band(n, 3)
            for e in range(1,n+1):
                sharp, _ = scan(n, 3, e, band=band, compare_raw=True)
                dyadic, _ = scan(n, 3, e)
                self.assertLessEqual(sharp["visited_blocks"], dyadic["visited_blocks"])
                self.assertLessEqual(sharp["endpoint_divisions"], dyadic["endpoint_divisions"])
