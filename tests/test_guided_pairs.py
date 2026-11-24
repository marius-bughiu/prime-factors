from itertools import combinations
import json
from math import gcd, isqrt, prod
from pathlib import Path
import unittest

from experiments.gap_coverage import primes_through
from experiments.guided_pairs import anchor_from_roots, cover, input_probability_bound
from experiments.pair_class_search import check_source, search
from experiments.same_source_pairs import direct_fractions


class GuidedPairTests(unittest.TestCase):
    def test_planted_full_size_anchor_and_comparisons(self):
        fixtures = Path(__file__).resolve().parents[1] / 'benchmarks/guided-pairs.json'
        fixture = next(r for r in json.loads(fixtures.read_text()) if r['id'] == 'guided-pair-planted-2048')
        n = int(fixture['n'])
        m = 2490290 * 2**883 * prod(p for p in primes_through(97) if p != 7)
        p, q = 2*m + 1, 3*m + 1
        self.assertEqual((p*q, n.bit_length(), p.bit_length(), q.bit_length()), (n, 2048, 1024, 1024))
        self.assertEqual(3*p - 2*q, 1)
        upper = isqrt(24*n + 1)
        self.assertEqual(upper*upper - 24*n, 1)
        self.assertEqual(gcd(upper-1, n), q)
        self.assertEqual(anchor_from_roots(n, upper, 1, 49), ((49, 1), (1, upper*upper//49)))
        work = search(n, 'unit', 0)
        self.assertTrue(check_source(n, 49, work))
        self.assertEqual((work['factor'], work['euclidean_states'], work['exact_pair_tests']), (q, 3, 1))
        self.assertEqual(cover(n, 48)['outcome'], 'no_split')
        fermat = (p+q)//2 - isqrt(n-1)
        self.assertGreater(fermat, 2**1017)
        self.assertLess(fermat, 2**1018)

    def test_cover_finds_gap_before_any_anchor_exists(self):
        n = 541*811
        work = cover(n, 49)
        self.assertEqual((work['multiplier'], work['upper_root'], work['gap_root']), (24, '3245', '1'))
        self.assertIn(work['factor'], (541, 811))
        self.assertIsNone(anchor_from_roots(n, 3245, 1, 54))
        self.assertEqual(anchor_from_roots(n, 3245, 1, 55), ((55, 1), (1, 191455)))
        self.assertEqual(cover(n, 49, 23)['outcome'], 'budget_exhausted')
        self.assertEqual(cover(n, 48)['outcome'], 'no_split')

    def test_second_square_at_multiplier_one(self):
        n = 17*31
        self.assertEqual((isqrt(n)+1)**2-n, 2)
        work = cover(n, 112)
        self.assertEqual((work['multiplier'], work['upper_root'], work['gap_root']), (1, '24', '7'))
        self.assertEqual((work['factor'], work['square_tests']), (17, 2))
        self.assertEqual(anchor_from_roots(n, 24, 7, 112), ((16, 7), (7, 36)))

    def test_minimum_generated_norm_matches_direct_fraction_census(self):
        primes = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
        for p, q in combinations(primes, 2):
            if p.bit_length() != q.bit_length():
                continue
            n = p*q
            units = {r for r in range(1, n) if gcd(r, n) == 1}
            direct = n
            for rows in direct_fractions(n, units).values():
                for (a, b), (c, d) in combinations(rows, 2):
                    product = a*b*c*d
                    if product > 0 and isqrt(product)**2 == product:
                        direct = min(direct, abs(a*b), abs(c*d))
            normalized = n
            for v in range(1, isqrt(n//2) + 1):
                for u in range(v+1, (n-1)//(2*v) + 1):
                    if (u*u-v*v) % n or gcd(u, v) != 1 or gcd(u*v, n) != 1:
                        continue
                    pair = anchor_from_roots(n, u, v, n//2)
                    self.assertIsNotNone(pair)
                    (a, b), (c, d) = pair
                    self.assertEqual((a*d-b*c) % n, 0)
                    self.assertEqual((gcd(a, b), gcd(c, d)), (1, 1))
                    self.assertTrue(2*max(a*b, c*d) < n)
                    self.assertEqual(a*b*c*d, (u*v)**2)
                    normalized = min(normalized, a*b, c*d)
            self.assertEqual(direct, normalized, (p, q))
            if direct < n:
                self.assertIn(cover(n, direct)['factor'], (p, q))

    def test_explicit_input_probability_bounds(self):
        for norm_bits, saving in ((48, 975), (1024, 483), (1940, 24)):
            self.assertLess(2**saving * input_probability_bound(norm_bits), 1)

    def test_finite_crt_conditions_for_the_50_form_family(self):
        coefficients = tuple(range(2501, 2551))
        plants = [p for p in primes_through(398059) if p > 382500]
        self.assertEqual((len(plants), plants[-1]), (1225, 398059))
        base, period = 0, prod(primes_through(50))
        for (a, b), prime in zip(combinations(coefficients, 2), plants):
            residue = -(a+b)*pow(2*a*b, -1, prime) % prime
            self.assertEqual((2*a*b*residue+a+b) % prime, 0)
            self.assertTrue(all((s*residue+1) % prime for s in coefficients))
            self.assertLess(8*a*b*(b-a)**2, prime**2)
            self.assertLess(prime**2, 2**38)
            base += period*((residue-base)*pow(period, -1, prime) % prime)
            period *= prime
        self.assertEqual((base.bit_length(), period.bit_length()), (22810, 22813))
        self.assertEqual(((2501*base+1)*(2502*base+1)).bit_length(), 45643)
