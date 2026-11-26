from collections import Counter
from unittest import TestCase

from experiments.cubic_smooth_bases import (SHIFTS, balanced_polynomial, candidate_bases, certificate,
                                          conventional, dyadic_witness, run_arm, smooth_values)
from experiments.cubic_trace_search import POINTS, characteristic, collect, evaluate, smooth_parity


class CubicSmoothBaseTests(TestCase):
    def test_band_order_degrees_and_deduplication(self):
        for n in (8, 64, 80, 989, 4097):
            values = smooth_values(n, 12)
            candidates = {2**i * 3**j for i in range(10) for j in range(13)
                          if n <= 8*(2**i*3**j)**3 and (2**i*3**j)**3 <= 8*n}
            self.assertEqual(set(values), candidates)
            for a, b in zip(values, values[1:]):
                if a < b:
                    self.assertLessEqual(8*n, (a+b)**3)
                else:
                    self.assertGreaterEqual(8*n, (a+b)**3)
            bases = candidate_bases(values)
            expected = {(s-t, t) for s in values for t in SHIFTS if s-t >= 2}
            self.assertEqual({(m, t) for m, tags in bases.items() for t in tags}, expected)
            offsets = conventional(n, bases.values())
            self.assertEqual(len(offsets), len(bases))
            self.assertEqual(list(offsets.values()), list(bases.values()))

    def test_norms_certificates_and_matched_counts(self):
        n = 989
        menu = candidate_bases(smooth_values(n, 2))
        arm = run_arm(n, menu)
        joint = designated = certified = 0
        for m, tags in menu.items():
            f = balanced_polynomial(n, m)
            self.assertEqual(evaluate(f, m), n)
            p = certificate(f, Counter())
            if p is None:
                continue
            self.assertTrue(all(evaluate(f, u) % p for u in range(p)))
            certified += 1
            joint += len(collect(m, f, POINTS, Counter()))
            for t in tags:
                norm = characteristic(f, (t, 1, 0))[2]
                self.assertEqual(norm, -evaluate(f, -t))
                self.assertEqual((norm+n) % (m+t), 0)
                self.assertIsNotNone(smooth_parity(t+m, Counter()))
                designated += int(smooth_parity(norm, Counter()) is not None)
        self.assertEqual(arm['all_rows']['visited'], certified*len(POINTS))
        self.assertEqual(arm['all_rows']['joint'], joint)
        self.assertEqual(arm['designated_rows']['joint'], designated)
        self.assertEqual(arm['designated_rows']['visited'], arm['designated_rows']['rational_smooth'])

    def test_reducible_cubic_skips_the_entire_row_budget(self):
        # n=m³ gives X³, which has a root at every certificate prime.
        arm = run_arm(64, {4: [0]})
        self.assertEqual(arm['work']['certified_bases'], 0)
        self.assertEqual(arm['all_rows']['visited'], 0)
        self.assertEqual(arm['work']['certificate_primes'], 25)

    def test_dyadic_compressed_witnesses_exhaust_all_units(self):
        for s in (4, 8, 16, 32, 128):
            for n in range(1, s, 2):
                witness = dyadic_witness(n, s)
                e, sign = int(witness['exponent']), witness['sign']
                actual = [(u, j) for u in (-1, 1) for j in range(s//4)
                          if (u*pow(5, j, s)+n) % s == 0]
                self.assertEqual(actual, [(sign, e)])
                self.assertLessEqual(int(witness['norm_bits_lower_bound']), (5**e).bit_length())
        for n, s in ((4, 16), (3, 12), (3, 2)):
            with self.assertRaises(ValueError):
                dyadic_witness(n, s)
