import unittest
from math import isqrt

from experiments.intermediate_totient_rows import product_band, scan
from experiments.midpoint_table_band import table_band, upper_endpoint
from experiments.scaled_power_menu import prefixes


class MidpointTableBandTests(unittest.TestCase):
    squares = tuple(j*j for j in range(256))

    def test_fold_even_upper_and_mersenne_boundaries(self):
        for bits in range(2, 8):
            lower = 1 << (bits - 1)
            mask = 2*lower - 1
            for n in range((mask + 1)**2):
                upper = min(lower + n//lower, mask + n//mask) & ~1
                self.assertEqual(upper_endpoint(n, bits), upper)

    def test_all_small_odd_products_and_shifted_square_boundaries(self):
        for bits in range(2, 9):
            odd = range((1 << (bits-1)) + 1, 1 << bits, 2)
            for p in odd:
                for q in odd:
                    observed = table_band(p*q, bits, self.squares)
                    self.assertEqual(observed, product_band(p*q, bits))
                    self.assertEqual(observed, table_band(p*q, bits, self.squares, interpolate=True))
                    self.assertLessEqual(observed[0], p+q-1)
                    self.assertLess(p+q-1, observed[1])

        for bits in (9, 12, 36, 1024):
            k = bits-8
            for j in (129, 191, 255):
                square = (j << k)**2
                for n in (square-1, square+1):
                    low, high = table_band(n, bits, self.squares)
                    exact_low, exact_high = product_band(n, bits)
                    self.assertLessEqual(low, exact_low)
                    self.assertLessEqual(exact_low-low, 2*((1 << k)-1))
                    self.assertEqual(high, exact_high)
                    chord, chord_high = table_band(n, bits, self.squares, interpolate=True)
                    self.assertLessEqual(low, chord)
                    self.assertLessEqual(chord, exact_low)
                    self.assertEqual(chord_high, high)
                    self.assertLessEqual(exact_low-chord, 6*(1 << max(0, k - 8)))
                    self.assertLessEqual(low, 2*(isqrt(n-1)+1)-1)

    def test_chord_error_at_both_ends_of_every_leading_word(self):
        # Width 16 has eight interpolated bits; every possible leading word appears here.
        for top in range(128**2, 256**2):
            for n in ((top << 16) + 1, ((top+1) << 16) - 1):
                low, high = table_band(n, 16, self.squares, interpolate=True)
                exact_low, exact_high = product_band(n, 16)
                self.assertLessEqual(low, exact_low)
                self.assertLessEqual(exact_low-low, 6)
                self.assertEqual(high, exact_high)

    def test_same_witness_as_exact_and_unrounded_at_each_exponent(self):
        for p, q in ((257, 263), (269, 491), (443, 503), (1291, 2003)):
            n, bits = p*q, p.bit_length()
            for _, exponent, _ in prefixes(n):
                if (exponent+1)**2 < 4*n:
                    continue
                witnesses = []
                for band in (None, product_band(n, bits), table_band(n, bits, self.squares),
                             table_band(n, bits, self.squares, interpolate=True)):
                    _, rows = scan(n, bits, exponent, band=band, price_full=False)
                    witnesses.append(sorted((key, row["a"], row["b"], row["t"], row["factor"])
                                            for key, row in rows.items()))
                self.assertEqual(witnesses[0], witnesses[1])
                self.assertEqual(witnesses[0], witnesses[2])
                self.assertEqual(witnesses[0], witnesses[3])


if __name__ == "__main__":
    unittest.main()
