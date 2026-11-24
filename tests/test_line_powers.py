import json
import unittest
from collections import Counter
from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path

from experiments.line_powers import search, trace_power


class LinePowerTests(unittest.TestCase):
    def test_ladder_matches_recurrence_over_composite_rings(self):
        for n in (4, 15, 35):
            for x in range(n):
                left, right = 2, x
                for d in range(41):
                    self.assertEqual(trace_power(x, d, n), left)
                    left, right = right, (x*right-left) % n

    def test_exact_collision_and_neutral_counts(self):
        for p in range(3, 72, 2):
            if any(p % j == 0 for j in range(2, isqrt(p)+1)):
                continue
            for d in range(1, 51):
                histogram = Counter(trace_power(x, d, p) for x in range(p))
                a, b = gcd(p-1, d), gcd(p+1, d)
                i, j = (p-1)//a, (p+1)//b
                count = (a*a*(2*i-gcd(i, 2)) + b*b*(2*j-gcd(j, 2))
                         + 2*a*b*gcd(i, j, 2))
                self.assertEqual(4*sum(c*c for c in histogram.values()), count)
                self.assertEqual(2*histogram[2], a+b)

    def test_divisor_bound_constant(self):
        primes = (p for p in range(2, 729) if all(p % i for i in range(2, isqrt(p)+1)))
        constant = prod(max(Fraction((2*e+1)**6, p**e) for e in range(10)) for p in primes)
        self.assertLess(constant, 2**247)
        self.assertLessEqual(21**6, 2*19**6)
        self.assertLess(24*1511*710*10000, 2**20*1000*22**2)

    def test_opposite_shift_fixture(self):
        path = Path(__file__).resolve().parents[1] / 'benchmarks' / 'line-powers.json'
        cases = json.loads(path.read_text())
        fixture = cases[0]
        p, q = map(int, fixture['factors'])
        n, d = p*q, (p*q)**2-1
        A, B, t = 1047655942105215289, 2**62, 83023756
        u = (A+B)*(B-A)*t*2**300
        a, b = A*u+1, B*u+1
        self.assertEqual((2*a*b-1, 1+2*B**2*(u//(B-A))*a), (p, q))
        self.assertEqual((p.bit_length(), q.bit_length(), n.bit_length()), (1024, 1024, 2048))
        self.assertEqual(d % (p+1), 0)
        self.assertTrue(d % (q+1) and d % (q-1))
        self.assertEqual([((p+1)//gcd(p+1,n+j)).bit_length() for j in (-1, 1)], [511, 513])
        self.assertEqual(search(n, 'square-1', 15, 1)['factor'], p)
        self.assertIsNone(search(n, 'square-1', 3, 0)['seed'])

        prior = json.loads(path.with_name('predecessor-square.json').read_text())
        source = next(case for case in prior if case['id'] == 'predecessor-square-2048')
        partner = next(int(r) for r in source['factors'] if (p*int(r)).bit_length() == 2048)
        control = next(case for case in cases if case['id'] == 'dickson-crossed-control-2048')
        self.assertEqual(int(control['n']), p*partner)
        self.assertNotEqual((partner**2-1) % (p+1), 0)
