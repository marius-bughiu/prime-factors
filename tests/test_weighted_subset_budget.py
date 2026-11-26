from itertools import combinations
from math import gcd
import unittest

from experiments.weighted_subset_budget import (
    DENOMINATOR, PRECISION, WHEEL, bound, prime_bins, reciprocal_upper, wheel_below,
)


class WeightedSubsetBudgetTests(unittest.TestCase):
    def test_possible_prime_supports_are_dominated(self):
        primes = (2, 3, 5, 7, 11, 13, 17, 19, 23)
        for budget in range(1, 18):
            earliest = [low for low, count in prime_bins(budget) for _ in range(count)]
            for size in range(len(primes) + 1):
                for support in combinations(primes, size):
                    if sum(p.bit_length() - 1 for p in support) <= budget:
                        self.assertLessEqual(size, len(earliest))
                        self.assertTrue(all(a <= p for a, p in zip(earliest, support)))

    def test_wheel_boundaries_and_fixed_point_rounding(self):
        for origin in (0, WHEEL - 11, 2**16 - 7, 2**34 - 13):
            actual = sum(gcd(n, WHEEL) == 1 for n in range(origin, origin + 32))
            self.assertEqual(wheel_below(origin + 32) - wheel_below(origin), actual)
        threshold = 2**(PRECISION * DENOMINATOR)
        for base in (2, 4, 65_536, 2**34 + 1):
            for exponent in (32, 43, 52, 63):
                rounded = reciprocal_upper(base, exponent)
                self.assertLess((rounded - 1)**DENOMINATOR * base**exponent, threshold)
                self.assertLessEqual(threshold, rounded**DENOMINATOR * base**exponent)

    def test_published_finite_bounds(self):
        for cap, support, fiber, savings in (
            (16, 642_914, 693, 294),
            (64, 10_168_464, 783, 201),
            (256, 162_721_256, 842, 139),
            (1024, 2_612_841_637, 884, 94),
            (4096, 41_990_647_392, 915, 60),
        ):
            with self.subTest(cap=cap):
                row = bound(cap, cap)
                self.assertEqual(row['support_bits'], support)
                self.assertEqual(row['absolute_excess_values_bits'], fiber)
                self.assertEqual(row['fraction_below_inverse_two_power'], savings)
