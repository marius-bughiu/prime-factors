from fractions import Fraction
from math import gcd, isqrt
import unittest

from experiments.weighted_windows import weighted_window


class FareyWindowTests(unittest.TestCase):
    def test_modular_inverse_finds_the_actual_neighbors_including_endpoints(self):
        for k in range(1, 21):
            slopes = sorted(Fraction(a, b) for b in range(1, k+1)
                            for a in range(b, 2*b+1) if gcd(a, b) == 1)
            for i, slope in enumerate(slopes):
                a, b = slope.numerator, slope.denominator
                for n in (35, 101*193, 6091663632054090929):
                    radicand = 4*a*b*n
                    endpoints = []
                    for j in (i-1, i+1):
                        if 0 <= j < len(slopes):
                            neighbor = slopes[j]
                            u, v = a+neighbor.numerator, b+neighbor.denominator
                            # At the mediant, the squared weighted sum is exactly
                            # n*(a*v+b*u)^2/(u*v). Take its integer square root.
                            endpoints.append(isqrt(n*(a*v+b*u)**2//(u*v)))
                    self.assertEqual(weighted_window(n,k,a,b),
                                     (1+isqrt(radicand-1), max(endpoints)))

    def test_coverage_on_both_sides_and_at_mediants(self):
        for k in range(1, 8):
            slopes = [(a,b) for b in range(1, k+1)
                      for a in range(b, 2*b+1) if gcd(a,b) == 1]
            for p in range(5, 40, 2):
                for q in range(p, 2*p+1):
                    n = p*q
                    if gcd(n, 6) != 1:
                        continue
                    covered = False
                    for a, b in slopes:
                        low, high = weighted_window(n,k,a,b)
                        t = a*p+b*q
                        if low <= t <= high:
                            s = gcd(24, 2*(a+b*n))
                            self.assertEqual((t-a-b*n) % s, 0)
                            covered = True
                    self.assertTrue(covered, (p,q,k))
