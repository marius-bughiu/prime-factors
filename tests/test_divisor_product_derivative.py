import unittest
from itertools import combinations
from math import gcd, isqrt, prod

from experiments.divisor_product_derivative import compare, search


class DivisorProductDerivativeTest(unittest.TestCase):
    def test_vanishing_product_and_unit_derivative_still_split(self):
        xs = [9, 11, 13, 15]
        n = 143
        result = compare(n, len(xs))
        digit = result['digit']
        derivative = sum(prod(xs)//x for x in xs)
        self.assertEqual((result['whole_band']['gcd'], gcd(derivative, n)), ('143', 1))
        self.assertEqual((digit['digit0'], digit['digit1'], digit['factor_sum']), ('135', '86', '24'))
        self.assertEqual((digit['factor'], result['through_sqrt']['gcd']), (11, '11'))

    def test_budgets_and_a_single_factor(self):
        for cap, outcome, factor in ((0, 'coprime_product', None), (1, 'coprime_product', None),
                                     (2, 'product_gcd', 11), (4, 'digit_sum', 11)):
            work = search(143, cap)
            self.assertEqual((work['outcome'], work['factor']), (outcome, factor))
            self.assertEqual(int(work['remaining'])+work['candidates'], 4)
            self.assertEqual(work['products'], 2 if cap == 4 else 1)

    def test_against_direct_residues_across_prime_pairs(self):
        primes = [n for n in range(5, 128, 2) if all(n % k for k in range(2, isqrt(n)+1))]
        for p, q in combinations(primes, 2):
            if p.bit_length() != q.bit_length():
                continue
            n = p*q
            w = search(n, 64)
            first, length = int(w['first']), int(w['full_candidates'])
            xs = range(first, first+2*length, 2)
            self.assertEqual(int(w['digit0']), prod(xs) % (n*n)//n)
            self.assertEqual(int(w['digit1']), prod(x+n for x in xs) % (n*n)//n)
            self.assertEqual((w['factor'], int(w['factor_sum'])), (p, p+q))
