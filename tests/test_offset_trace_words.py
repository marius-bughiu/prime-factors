from math import gcd, isqrt
import unittest

from experiments.offset_trace_words import index_masks, repeated_mask, search
from experiments.offset_winner_window import bounds, coordinate_range


class OffsetTraceWordsTests(unittest.TestCase):
    def test_bit_positions_match_direct_discriminants(self):
        n = 117449
        t = isqrt(n)
        primes = [5, 7, 11]
        squares = {p: {x*x % p for x in range(p)} for p in primes}
        masks = index_masks(n, t, primes, dict(unit_inverses=0, mask_entries=0))
        for p in primes:
            for k in range(1, p):
                for first in range(2*p):
                    width = 2*p+3
                    word = repeated_mask(masks[p, k], p, first, width)
                    expected = [i for i in range(width) if
                                ((first+2*i+2*t*k)**2-4*n*k*k) % p in squares[p]]
                    self.assertEqual([i for i in range(width) if (word >> i) & 1], expected)

    def test_complete_charts_preserve_oriented_winners(self):
        for p, q in [(37, 59), (71, 127), (257, 457)]:
            n = p*q
            box = bounds(n)
            t, kmax = box['T'], box['K']
            expected = []
            for v in range(1, isqrt(kmax)+1):
                for s in coordinate_range(t, box['L'], kmax, v):
                    k = s*v
                    j = p*s*s+q*v*v-2*t*k
                    if gcd(s, v) == gcd(j, k) == 1 and 0 < j <= box['J']:
                        expected.append([j, k, s, v])
            run = search(n, prime_limit=31)
            self.assertTrue(run['exhaustive'])
            self.assertEqual(run['proper_hits'], len(expected))
            self.assertIn(run['first_hit'], expected)
            self.assertEqual(run['factor'], p)

    def test_caps_precede_large_word_allocation(self):
        guard = search(502005281288939, max_word_bits=100)
        self.assertEqual((guard['outcome'], guard['mask_entries'], guard['raw_pairs']), ('word_cap', 0, 0))
        self.assertGreater(guard['word_bits_required'], guard['max_word_bits'])
        partial = search(117449, max_pairs=2)
        self.assertFalse(partial['exhaustive'])
        self.assertEqual(partial['raw_pairs'], 2)
        self.assertGreater(partial['unvisited_upper'], 0)
        self.assertEqual(search(117449, max_pairs=0)['mask_entries'], 0)

    def test_setup_prime_and_square(self):
        self.assertEqual(search(17*31)['factor'], 17)
        self.assertEqual(search(21**2)['factor'], 21)
