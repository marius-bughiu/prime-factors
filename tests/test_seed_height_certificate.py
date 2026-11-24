from math import gcd
import unittest

from experiments.seed_height_certificate import certificate, crossed_factors


class SeedHeightCertificateTests(unittest.TestCase):
    def test_euclidean_minimum_against_every_denominator(self):
        for p, q in ((5, 7), (7, 11), (11, 13), (13, 17), (19, 23), (23, 31)):
            n = p*q
            report = certificate(p, q)
            z = int(report['mixed_root'])
            minimum = min(b * min(z*b % n, -z*b % n) for b in range(1, n))
            self.assertEqual(int(report['min_product']), minimum)
            self.assertEqual(int(report['lower']), 2*minimum**2 // n + 1)
            (a,b), (c,e) = [list(map(int, row)) for row in report['fractions']]
            self.assertEqual(int(report['upper']), min(a*b, c*e))
            self.assertLess(2*max(a*b, c*e), n)
            self.assertEqual((a*e-b*c) % n, 0)
            self.assertEqual(a*b*c*e, minimum**2)
            self.assertIn(gcd(int(report['source'])*b*e-minimum, n), (p,q))

    def test_full_size_threshold_and_attainment(self):
        report = certificate(*crossed_factors())
        lower, upper = int(report['lower']), int(report['upper'])
        self.assertEqual((lower.bit_length(), upper.bit_length()), (2031, 2031))
        self.assertLess(upper*100, lower*102)
        self.assertEqual((report['euclidean_steps'], report['divisor']), (1134, 213))
