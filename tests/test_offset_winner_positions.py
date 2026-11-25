"""Compare known-factor predictions with a product-only exhaustive search."""

import unittest

from experiments.complete_offset_search import search
from experiments.offset_winner_positions import winner_positions
from scripts.factor import primes_through


class OffsetWinnerPositionTests(unittest.TestCase):
    def test_reduced_basis_predicts_all_hits_and_first_raw_rank(self):
        primes = [p for p in primes_through(255) if p >= 17]
        for i, p in enumerate(primes):
            for q in primes[i+1:]:
                if q > 2*p:
                    break
                n = p*q
                predicted = winner_positions(n, p, q)
                entire = search(n, predicted['raw_slots'], exhaust=True)
                self.assertEqual(len(predicted['winners']), entire['proper_hits'])
                first = predicted['winners'][0]
                self.assertEqual((first['j'], first['k']),
                                 (entire['first_hit']['j'], entire['first_hit']['k']))
                self.assertEqual(search(n, first['raw_rank']-1)['factor'], None)
                self.assertEqual(search(n, first['raw_rank'])['factor'], first['factor'])

    def test_report_uses_fixed_orientation(self):
        row = winner_positions(1891, 31, 61)
        self.assertEqual([(w['j'], w['k'], w['factor']) for w in row['winners']],
                         [(6, 1, 31), (7, 6, 61)])
