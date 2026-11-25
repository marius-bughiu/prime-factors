"""Regression checks for the integer offset schedule and its explicit budget."""

from math import gcd, isqrt
import unittest

from experiments.complete_offset_search import census, search, slot_count


class CompleteOffsetTests(unittest.TestCase):
    def test_floor_sum_counts_every_slot_including_final_one(self):
        for T in range(1, 17):
            for h in range(1, 2*T+2):
                for J in range(0, 12):
                    expected = sum(T*j//h+1 for j in range(1, J+1))
                    self.assertEqual(slot_count(T, h, J)[0], expected)

    def test_only_success_needs_negative_residual_in_final_slot(self):
        result = search(117449, 241, exhaust=True)
        self.assertEqual(result['unvisited_pairs'], 0)
        self.assertEqual(result['visited_pairs'], 241)
        self.assertEqual((result['last_slot_hits'], result['interior_hits']), (1, 0))
        self.assertEqual(result['first_hit'], dict(j=17, k=12, residual=-6, delta=1,
                                                   square_root=1, last_slot=True))
        self.assertEqual({result['factor'], result['remaining']}, {257, 457})

    def test_census_recovers_every_distinct_prime_pair(self):
        for bits, products, last_only in ((7, 78, 0), (8, 253, 0), (9, 903, 8)):
            with self.subTest(bits=bits):
                result = census(bits)
                self.assertEqual((result['products'], result['only_last_slot']), (products, last_only))

    def test_cap_is_on_raw_visits_and_preserves_next_position(self):
        n = 117449
        for cap in (0, 1, 37, 115):
            run = search(n, cap)
            self.assertEqual(run['status'], 'partial')
            self.assertIsNone(run['factor'])
            self.assertEqual(run['remaining'], n)
            self.assertEqual(run['visited_pairs'], cap)
            self.assertEqual(run['unvisited_pairs'], run['raw_pairs']-cap)
            j, k = run['next_pair']
            self.assertEqual(slot_count(run['root'], run['offset'], j-1)[0]+k-1, cap)
        self.assertEqual(search(n, 116)['status'], 'split')
        square = search(49, 0)
        self.assertEqual((square['factor'], square['remaining'], square['visited_pairs']), (7, 7, 0))

    def test_signed_gap_agrees_with_weighted_sum_square(self):
        for n in (17, 91, 9017, 117449):
            T = isqrt(n)
            h = n-T*T
            run = search(n, 65536, exhaust=True)
            hits = negative = primitive = squares = 0
            for j in range(1, run['max_offset']+1):
                for k in range(1, T*j//h+2):
                    if gcd(j, k) != 1:
                        continue
                    primitive += 1
                    weight = j+2*T*k
                    gap = weight*weight-4*k*k*n
                    negative += gap < 0
                    if gap >= 0 and isqrt(gap)**2 == gap:
                        squares += 1
                        hits += 1 < gcd((weight-isqrt(gap))//2, n) < n
            self.assertEqual((run['proper_hits'], run['negative_discriminants'],
                              run['coprime_pairs'], run['square_hits']),
                             (hits, negative, primitive, squares))
