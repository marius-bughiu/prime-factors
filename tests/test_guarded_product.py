import unittest

from experiments.bit_marginals import Table, contract, multiplier_tables
from experiments.guarded_product import compare, guarded_multiplier
from experiments.quarter_residue import ModularCounter, read_residue


def count_with_pinned_inputs(net, x, y):
    pins = [(wire, (value >> i) & 1)
            for value, wires in ((x, net.xs), (y, net.ys)) for i, wire in enumerate(wires)]
    net.tables.extend(Table(wire, {wire * bit: 1}) for wire, bit in pins)
    count, _ = contract(net, ModularCounter(3))
    del net.tables[-len(pins):]
    return count


class GuardedProductTests(unittest.TestCase):
    def test_high_columns_really_are_absent(self):
        partial = multiplier_tables(143, 4, output_bits=6)
        guarded, patterns, rows = guarded_multiplier(143, 4, 2)
        self.assertEqual(patterns, 64)
        self.assertTrue(0 < rows <= patterns)
        # 3*5=15 and 143 agree modulo 64. Only the guard removes this alias.
        self.assertEqual(count_with_pinned_inputs(partial, 3, 5), 1)
        self.assertEqual(count_with_pinned_inputs(guarded, 3, 5), 0)
        self.assertEqual(count_with_pinned_inputs(guarded, 11, 13), 1)

    def test_all_two_bit_targets_and_input_pairs(self):
        for n in range(16):
            net, _, _ = guarded_multiplier(n, 2, 1)
            for x in range(4):
                for y in range(4):
                    with self.subTest(n=n, x=x, y=y):
                        self.assertEqual(count_with_pinned_inputs(net, x, y), int(x * y == n))

    def test_guard_preserves_ordered_residue(self):
        for n, width, expected in [(51, 6, 1), (143, 8, 1), (323, 5, 3), (36, 4, 3)]:
            result = compare(n, width)
            for row in (result["full"], *result["guarded"]):
                self.assertEqual(int(row["residue"]), expected)
                self.assertLessEqual(row["guard_patterns"], 256)
            if width == n.bit_length():
                self.assertEqual(result["full"]["matched_rows"], read_residue(n)["matched_rows"])

    def test_large_top_table_is_rejected_before_construction(self):
        with self.assertRaises(ValueError):
            guarded_multiplier(143, 1024, 512)
