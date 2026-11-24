import unittest

from experiments.quarter_residue import (
    compare_bit_queries, decode_unit, read_residue, read_unit_residue, run_fixtures,
)


class QuarterResidueTests(unittest.TestCase):
    def test_unit_decoder_inverts_all_small_unit_codes(self):
        for k in range(1, 11):
            modulus = 1 << k
            for odd in range(1, modulus, 2):
                scalar = (-1 if odd & 2 else 1) * pow(5, odd // 4, modulus) % modulus
                self.assertEqual(decode_unit(scalar, k), odd)
            self.assertIsNone(decode_unit(0, k))

    def test_fused_weights_and_nontrivial_lift(self):
        # 12827 = 101 * 127, and the scalar 3 encodes 127 mod 16 = 15.
        compared = compare_bit_queries(12827, balanced=True, include_units=True)
        unit = compared["unit_tags"]
        self.assertEqual((unit["scalar"], unit["residue"]), ("3", "15"))
        self.assertEqual(unit["residue"], compared["single"]["residue"])
        self.assertEqual(unit["residue"], compared["bit_queries"]["residue"])
        self.assertEqual(unit["tagged_entries"], 2 * (unit["k"] - 1))
        self.assertEqual(compared["bit_queries"]["assuming_odd_pair"]["calls"], 3)

    def test_unit_controls(self):
        self.assertEqual(read_unit_residue(15)["residue"], "1")
        empty_box = read_unit_residue(51, balanced=True)
        self.assertEqual((empty_box["status"], empty_box["residue"]), ("unresolved", None))
        self.assertIsNone(read_unit_residue(17)["residue"])
        self.assertIsNone(read_unit_residue(6)["residue"])
        # 105 has three selected pairs. Its unit is decodable but fails
        # the unique-pair assumption, which the output states explicitly.
        alias = read_unit_residue(105)
        self.assertEqual((alias["scalar"], alias["status"]), ("3", "conditional"))

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
