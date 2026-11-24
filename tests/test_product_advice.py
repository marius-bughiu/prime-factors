from collections import Counter, defaultdict
from math import gcd, isqrt
import unittest

from experiments.gap_coverage import primes_through
from experiments.product_advice import coverage


class ProductAdviceTests(unittest.TestCase):
    def test_two_slot_optimum_against_direct_midpoints(self):
        bits = 6
        x = 1 << (bits - 1)
        primes = [p for p in primes_through(2*x) if p >= x]
        options = {}
        for m in range(1, x):
            modulus = m*m
            roots = sum(gcd(u, modulus) == 1 and u*u % modulus == 1 % modulus
                        for u in range(modulus))
            if roots <= 2:
                options[m] = 2//roots
        for k in (0, 2, bits - 1):
            cells = defaultdict(Counter)
            for i, p in enumerate(primes):
                for q in primes[i+1:]:
                    n = p*q
                    if n < 2*x*x:
                        continue
                    start = isqrt(n-1) + 1
                    row = cells[n >> (bits+k), n % (1 << k)]
                    for m, count in options.items():
                        for h in range(start, start+m*m*count):
                            if h*h % (m*m) == n % (m*m) and h == (p+q)//2:
                                row[m] += 1
            expected = sum(max(row.values(), default=0) for row in cells.values())
            self.assertEqual(coverage(bits, [k])['with_advice'][k], expected)
