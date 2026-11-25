import unittest
from math import gcd, isqrt

from experiments.gap_coverage import primes_through
from experiments.neighbor_smooth_sum import search
from experiments.smooth_factor_sums import scan_two_three, smooth_sum_bounds


class NeighborSmoothSumTest(unittest.TestCase):
    def test_public_sum_and_weighted_comparison(self):
        p, q = 2101249, 3658751
        n = p*q
        run = search(n, 5)
        self.assertEqual((run['factor'], run['smooth_part']), (p, str(p+q)))
        self.assertEqual((run['remainder_checks'], run['square_tests']), (19, 1))
        self.assertEqual((p+q)//2 - isqrt(n), 107286)
        trials = []
        for a in range(1, 9):
            for b in range(1, 9):
                if gcd(a, b) != 1:
                    continue
                start = isqrt(4*a*b*n-1)+1
                start += (a+b-start) % 2
                trials.append(((a*p+b*q-start)//2+1, a, b))
                residual = start**2 - 4*a*b*n
                self.assertNotEqual(isqrt(residual)**2, residual)
        self.assertEqual(len(trials), 43)
        self.assertEqual(min(trials), (47, 7, 4))
        # The only candidate tested is the entire smooth part at each cutoff.
        self.assertIsNone(search(n, 31)['factor'])

    def test_unrelated_gap_can_select_the_sum(self):
        p, q = 2749, 3907
        n = p*q
        self.assertEqual(pow(p, -1, q) - pow(q, -1, p), -2088)
        for gap in (8, -8):
            run = search(n, 13, gap)
            self.assertEqual((run['factor'], run['smooth_part']), (p, str(p+q)))
        for gap in (0, 2, 4, 6):
            self.assertIsNone(search(n, 13, gap)['factor'])

    def test_smooth_sum_count_against_actual_integers(self):
        for bits in range(2, 12):
            low, high = smooth_sum_bounds(bits, 7, 32)
            actual = 0
            for candidate in range(2**bits, 2**(bits+1), 2):
                residual = candidate
                for prime in (2, 3, 5, 7):
                    while residual % prime == 0:
                        residual //= prime
                actual += residual == 1
            self.assertLessEqual(low, actual)
            self.assertLessEqual(actual, high)
        low, high = smooth_sum_bounds()
        self.assertEqual((low, high), (1656965853583758893, 1676749662954303816))
        self.assertLess(44331 * high * 2**947, 2**1023)

    def test_direct_search_under_the_smooth_sum_promise(self):
        primes = primes_through(251)
        for p in primes:
            for q in primes:
                if p == 2 or p >= q or p.bit_length() != q.bit_length():
                    continue
                odd = p+q
                for prime in (2, 3):
                    while odd % prime == 0:
                        odd //= prime
                result = scan_two_three(p*q)
                self.assertEqual(result['factor'], p if odd == 1 else None)
