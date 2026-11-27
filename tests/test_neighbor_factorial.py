from itertools import combinations
from math import gcd, isqrt, prod
import unittest

from experiments.neighbor_factorial import RESIDUES, batch, filtered_terms, first_traces, search


def rising(x, width):
    return prod(range(x, x + width))


def determinant_three(rows):
    (a, b, c), (d, e, f), (g, h, i) = rows
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def nine_bit_prime_pairs():
    primes = [
        n for n in range(257, 512)
        if all(n % d for d in range(2, isqrt(n) + 1))
    ]
    return combinations(primes, 2)


class NeighborFactorialTest(unittest.TestCase):
    def test_original_determinants_include_a_saturation(self):
        for x, expected in ((6, 1), (7, 11), (9, 143)):
            rows = [[rising(x + i, w) for w in (0, 2, 5)] for i in range(3)]
            self.assertEqual(gcd(determinant_three(rows), 143), expected)
            self.assertEqual(gcd(30 * rising(x + 1, 4), 143), expected)

    def test_skipped_row_identity(self):
        for x in (1, 6, 46, 193):
            for w in range(3, 12):
                rows = [[1, x + i, rising(x + i, w)] for i in (0, 1, 3)]
                expected = w * (w - 1) * rising(x + 3, w - 3) * (3 * x + w + 4)
                self.assertEqual(determinant_three(rows), expected)
        self.assertEqual(gcd(rising(46, 9), 2183), 1)
        self.assertEqual(gcd(3 * 46 + 10, 2183), 37)

    def test_filtered_batch_including_partial_periods(self):
        self.assertEqual(len(RESIDUES), 14)
        for p, q in nine_bit_prime_pairs():
            n = p * q
            for lo, hi in ((7, 9), (7, 78), (12, 86)):
                factor, work, _ = search(n, lo, hi)
                start = 3 * isqrt(n) + lo
                stop = start + hi - lo + 1
                raw, count = batch(n, range(start, stop))
                self.assertEqual(factor, raw if raw > 1 else None)
                self.assertNotEqual(raw, n)
                self.assertEqual(work["raw_terms"], count)
                self.assertEqual(work["filtered_terms"], len(list(filtered_terms(start, stop))))
                if hi - lo + 1 == 72:
                    self.assertEqual(work["filtered_terms"], 14)

    def test_both_short_hit_orientations_have_a_first_square(self):
        observed = set()
        for p, q in nine_bit_prime_pairs():
            n = p * q
            x = isqrt(n)
            traces, _ = first_traces(n)
            for c in range(7, isqrt(p - 1) + 1):
                g = gcd(3 * x + c, n)
                if g == 1:
                    continue
                kind = 1 if g == p else 0
                self.assertEqual(g, p if kind else q)
                self.assertIn(traces[kind], (str(p), str(q)))
                observed.add(kind)
        self.assertEqual(observed, {0, 1})

    def test_oversized_width_rejected(self):
        with self.assertRaises(ValueError):
            search(2183, 7, 78)
