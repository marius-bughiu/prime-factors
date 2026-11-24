import unittest

from experiments.quarter_residue import compare_bit_queries, read_residue, run_fixtures


class QuarterResidueTests(unittest.TestCase):
    def test_binary_queries_agree_on_semiprime(self):
        result = compare_bit_queries(77)
        self.assertEqual(result["bit_queries"]["residue"], result["single"]["residue"])
        self.assertEqual(result["bit_queries"]["calls"], result["single"]["k"])

    def test_semiprime_fixtures(self):
        for result in run_fixtures():
            with self.subTest(n=result["n"], balanced=result["balanced"]):
                self.assertGreater(result["matched_rows"], 0)
                self.assertEqual(result["remaining"], [result["n"]])

    def test_all_small_products_match_ordered_pair_sum(self):
        # The pair enumeration below is an independent test of the contraction.
        for n in [*range(1, 32), 36, 49, 65]:
            with self.subTest(n=n):
                result = read_residue(n)
                width = result["width"]
                expected = sum(y for x in range(2, 1 << width)
                               for y in range(x, 1 << width) if x * y == n)
                self.assertEqual(int(result["residue"]), expected % int(result["modulus"]))
                self.assertEqual(result["k"], (n.bit_length() + 3) // 4)
