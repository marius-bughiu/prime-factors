import unittest
from math import isqrt

from experiments.crt_square_norms import _local_roots, _nearby, _split_roots, search


class CrtSquareNormTest(unittest.TestCase):
    def test_split_lists_and_window_match_all_brute_force_roots(self):
        # Include an empty half, thresholds spanning several periods, zero
        # thresholds, and root-free intervals when the modulus dominates N.
        for n, count in ((10, 1), (82, 1), (211, 3), (1009, 2), (26827, 2), (21490481, 2)):
            roots, factor = _local_roots(n, count, dict(primes_tested=0))
            self.assertIsNone(factor)
            d, lefts, rights = _split_roots(roots)
            modulus = d*d
            residues = [t for t in range(modulus) if (t*t-n) % modulus == 0]
            self.assertEqual(sorted((l+r) % modulus for l in lefts for r in rights), residues)
            for bound in (0, 1, isqrt(n)//2, 8*isqrt(n)):
                stop = isqrt(n + modulus*bound) + 1
                # One full period on the upper side of sqrt(n) contains a root.
                search_stop = max(stop, isqrt(n)+modulus+1)
                solutions = [t for t in range(search_stop) if (t*t-n) % modulus == 0]
                expected = [t for t in solutions if abs(t*t-n) <= bound*modulus]
                want_best = min((abs(t*t-n)//modulus, t) for t in solutions)
                for cap in (0, 1, len(expected)+1):
                    norm, nearest, total, hits = _nearby(n, d, lefts, rights, bound, cap)
                    with self.subTest(n=n, bound=bound, cap=cap):
                        self.assertEqual((norm, nearest), want_best)
                        self.assertEqual(total, len(expected))
                        self.assertEqual(len(set(hits)), min(cap, total))
                        self.assertTrue(set(hits) <= set(expected))

    def test_negative_pair_requires_both_hits(self):
        work = search(26827, 2, 0, 2)
        self.assertEqual((work['primes'], work['interval_hits'], work['factor']),
                         ([3, 11], 2, 139))
        self.assertEqual(work['selected_steps'], ['85', '157'])
        short = search(26827, 2, 0, 1)
        self.assertEqual((short['interval_hits'], short['visited_hits']), (2, 1))
        self.assertTrue(short['hit_cap_reached'])
        self.assertIsNone(short['factor'])
        self.assertEqual(work['min_abs_norm'], short['min_abs_norm'])

    def test_rotating_triples_respect_the_shared_cap(self):
        n = 367722817904017001243509
        short = search(n, 12, -4, 1000, 3)
        self.assertIsNone(short['factor'])
        self.assertTrue(short['hit_cap_reached'])
        result = search(n, 12, -4, 5138, 3)
        self.assertEqual(result['windows'], 8)
        self.assertEqual(result['total_windows'], 220)
        self.assertEqual((result['interval_hits'], result['materialized_hits'],
                          result['visited_hits']), (1024, 1024, 1001))
        self.assertEqual(result['selected_steps'], [['795', '606403027147']])
        self.assertEqual(result['factor'], 605056390957)
        with self.assertRaises(ValueError):
            search(n, 4, 0, 100, 5)

    def test_widening_scales_the_real_square_root_before_rounding(self):
        # floor(4 sqrt(7)) = 10; using four times floor(sqrt(7)) loses t=4.
        work = search(7, 0, -2, 10)
        self.assertEqual(work['interval_hits'], 5)

    def test_input_validation_and_early_gcd(self):
        self.assertEqual(search(14, 1, 2, 2)['factor'], 2)
        self.assertEqual(search(49, 1, 2, 2)['factor'], 7)
        self.assertEqual(search(33, 2, 1, 2)['outcome'], 'prime_divisor')
        self.assertEqual(search(3, 1, 0, 2)['factor'], None)
        self.assertEqual(search(2, 1, 0, 2)['factor'], None)
        for args in ((1, 1, 2, 3), (3, -1, 2, 3), (3, 1, 2, -3)):
            with self.assertRaises(ValueError):
                search(*args)
