import unittest
from unittest.mock import patch

from experiments.dyadic_totative_masks import check_contrasts, search


class DyadicTotativeMaskTests(unittest.TestCase):
    def test_cap_is_inclusive_and_stops_before_next_coefficient(self):
        limited = search(53 * 59, 389)
        self.assertEqual([row["gcd"] for row in limited["rows"]], ["3127"])
        self.assertEqual(limited["stopped_before"], 3)
        self.assertEqual(limited["next_row_bits"], (390).bit_length())
        self.assertEqual(limited["remaining"], ["3127"])
        exact = search(53 * 59, 390)
        self.assertEqual(exact["factors"], ["53", "59"])
        self.assertEqual(exact["remaining"], [])

    def test_full_size_stop_happens_before_binomial_or_gcd(self):
        with patch("experiments.dyadic_totative_masks.comb", side_effect=AssertionError), \
             patch("experiments.dyadic_totative_masks.gcd", side_effect=AssertionError):
            n = (1 << 2047) + 1
            result = search(n, 4096)
        self.assertEqual(result["rows"], [])
        self.assertEqual(result["remaining"], [str(n)])
        self.assertEqual((result["stopped_before"], result["next_row_bits"]), (1022, 1026))

    def test_small_contrasts_against_direct_coprimality_counts(self):
        self.assertEqual(check_contrasts(1763, 41, 43), 6)
        self.assertEqual([row["gcd"] for row in search(1763, 881)["rows"]],
                         ["1", "1763", "1", "41"])


if __name__ == "__main__":
    unittest.main()
