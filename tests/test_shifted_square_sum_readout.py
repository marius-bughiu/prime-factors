import unittest

from experiments.shifted_square_sum_readout import search
from scripts.render_site import case_row


class ShiftedSquareSumReadoutTests(unittest.TestCase):
    def test_predictions_match_all_shifted_roots(self):
        for bits in (6, 8):
            modulus = 1 << (bits + 1)
            for residue in range(1, modulus, 8):
                n = (1 << (2 * bits - 2)) + residue
                actual = search(n, bits)
                sums = {2 * half % modulus for half in range(modulus)
                        if (half * half - n) % modulus == modulus // 8}
                with self.subTest(bits=bits, residue=residue):
                    self.assertEqual(actual['sum_predictions'], sorted(sums))
                    self.assertEqual(actual['candidate_sum'], max(sums))
                    self.assertEqual(actual['integer_sum_checks'], 1)

    def test_matched_products_share_prediction_and_have_different_outcomes(self):
        hit = search(601049, 10)
        miss = search(842713, 10)
        self.assertEqual(hit['candidate_sum'], miss['candidate_sum'])
        self.assertEqual(hit['factor'], 619)
        self.assertIsNone(miss['factor'])
        self.assertLess(miss['discriminant'], 0)

    def test_report_displays_both_signed_discriminants(self):
        for n, factors, discriminant in [(601049, ['619', '971'], '123,904'),
                                         (842713, [], '-842,752')]:
            with self.subTest(n=n):
                row = dict(id='example', description='Sum prediction', bits=n.bit_length(),
                           method='shifted-square-sum-readout', shifted_square_sum_readout=search(n, 10),
                           n=str(n), verified=bool(factors), factors=factors,
                           remaining=[] if factors else [str(n)], certificate='proofs/example.lean',
                           wall_seconds=0.1, verification_seconds=0.01)
                report = case_row(row)
                self.assertIn('predicted sum 1,590', report)
                self.assertIn('discriminant ' + discriminant, report)
                self.assertIn('Lean checked' if factors else 'Remaining cofactor(s)', report)


if __name__ == '__main__':
    unittest.main()
