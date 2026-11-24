import unittest
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, prod

from experiments.gap_coverage import primes_through
from experiments.mixed_ratio_heights import jacobi
from experiments.norm_direction_check import check_labels, prime_root
from experiments.norm_directions import (
    admissible_multipliers, arc, discriminants, input_failure_bound, scan, search,
)
from experiments.seed_height_certificate import crossed_factors


def positive_points(total, a, b):
    """Enumerate a*x² + b*y² = total by checking each possible positive y."""
    for y in range(1, isqrt((total-1)//b)+1):
        square, remainder = divmod(total-b*y*y, a)
        x = isqrt(square)
        if not remainder and x*x == square:
            yield x, y


class NormDirectionsTests(unittest.TestCase):
    def test_pivot_list_preserves_all_solvable_generator_products(self):
        # Test existence against all subsets and literal squares in each field.
        primes = primes_through(70)
        labels = [p for p in primes if p > 13]
        residues = {p: {x*x % p for x in range(1, p)} for p in labels}
        for length in (1, 2, 4, 6):
            generators = primes[:length]
            products = [prod(row) for k in range(length+1)
                        for row in combinations(generators, k)]
            for p, q in combinations(labels, 2):
                public, factor = discriminants(p*q, generators)
                with self.subTest(length=length, p=p, q=q):
                    self.assertIsNone(factor)
                    self.assertEqual(len(public), len(set(public)))
                    self.assertLessEqual(len(public), length+1)
                    self.assertTrue(all(jacobi(-d, p*q) == 1 for d in public))
                    def represented(d):
                        return -d % p in residues[p] and -d % q in residues[q]
                    self.assertEqual(any(map(represented, public)),
                                     any(map(represented, products)))
        self.assertEqual(discriminants(7*31, [2, 3, 5, 7, 11]), ([], 7))

    def test_complete_scan_matches_every_positive_representation(self):
        for total in range(1, 145):
            for d in (1, 2, 3, 4, 7, 14):
                work = Counter()
                points = list(scan(total, d, 1, work, 1000))
                with self.subTest(total=total, d=d):
                    self.assertCountEqual(points, positive_points(total, 1, d))
                    positions = 0 if total < 1+d else isqrt(total//2)+isqrt(total//(2*d))
                    self.assertEqual(work['coordinate_positions'], positions)
        # The equality chart has two descriptions, but occurs exactly once.
        self.assertEqual(list(scan(36, 4, 2, Counter(), 100)).count((6, 3)), 1)

    def test_wide_arc_blocks_recover_all_points_including_endpoints(self):
        for a, b, x, y in ((1, 1, 51, 68), (7, 1, 21, 86), (1, 14, 83, 22)):
            total = a*x*x+b*y*y
            last = isqrt(total//(2*a))
            expected = {(u, v) for u, v in positive_points(total, a, b) if u <= last}
            for width in (1, 6, 17, last):
                found = []
                work = Counter()
                for lo in range(1, last+1, width):
                    hi = min(lo+width-1, last)
                    found.extend(arc(total, a, b, lo, hi, work))
                with self.subTest(a=a, b=b, width=width):
                    self.assertCountEqual(found, expected)
                    self.assertGreaterEqual(work['line_tests'], work['discriminant_roots'])

    def test_block_budget_and_factor_outcomes(self):
        self.assertEqual(search(45, 2, 100)['outcome'], 'coordinate_gcd')
        self.assertEqual(search(21, 3, 0)['factor'], 3)
        self.assertEqual(search(15, 2, 0)['outcome'], 'no_split')
        self.assertEqual(search(3599, 13, 0)['blocks'], 0)
        full = search(3599, 13, 1000)
        short = search(3599, 13, full['blocks']-1)
        self.assertIsNone(short['factor'])
        self.assertEqual(short['outcome'], 'block_limit')
        self.assertEqual(short['blocks'], full['blocks']-1)
        self.assertEqual(search(3599, 13, full['blocks']), full)
        self.assertEqual({row[1] for row in full['witnesses']}, {1, 2})
        self.assertIn(full['factor'], (59, 61))
        for args in ((2, 13, 1), (10, 13, 1), (7, 1, 1), (7, 3, -1)):
            with self.assertRaises(ValueError):
                search(*args)

    def test_exact_character_cell_counts_and_conditional_bound(self):
        # Count signatures for every unit of a small complete period.
        primes = [2, 3, 5, 7]
        modulus = 4*prod(primes)
        cells = Counter(tuple(jacobi(g, u) for g in [-1]+primes)
                        for u in range(1, modulus, 2) if gcd(u, modulus) == 1)
        self.assertEqual(len(cells), 2**(len(primes)+1))
        self.assertEqual(set(cells.values()), {6})
        x = 2**1023
        partners = 6*((x+modulus-1)//modulus)
        expected = Fraction(3*1511*710*100**2*partners, 1000*22**2*x)
        self.assertEqual(input_failure_bound(primes), expected)
        self.assertLess(input_failure_bound(primes_through(739)), Fraction(1, 2**119))
        for invalid in ([], [3, 5], [2, 3, 3], [2, 9], [2, x+1]):
            with self.assertRaises(ValueError):
                input_failure_bound(invalid)

    def test_reduced_multiplier_screen_against_literal_residue_tables(self):
        for d in range(1, 65):
            moduli = [8]+[p for p in primes_through(d) if p != 2 and d % p == 0]
            tables = [{(t*t+d*a*a) % m for t in range(m) for a in range(m)}
                      for m in moduli]
            for n in range(3, 66, 2):
                expected = [k for k in range(1, d+1) if 3*k*k <= 4*d
                            and all(k*n % m in allowed for m, allowed in zip(moduli, tables))]
                self.assertEqual(list(admissible_multipliers(n, d)), expected, (n, d))

    def test_prime_roots_against_literal_squares(self):
        for p in primes_through(113)[1:]:
            squares = {x*x % p for x in range(1, p)}
            for residue in range(p):
                if residue in squares:
                    self.assertEqual(pow(prime_root(residue, p), 2, p), residue)
                else:
                    with self.assertRaises(ValueError):
                        prime_root(residue, p)

    def test_independent_label_witnesses(self):
        self.assertEqual(check_labels(7, 31, 7), {'trial_divisor': '7'})
        self.assertIsNone(check_labels(59, 61, 2)['d'])
        for p, q, bound in [(59, 61, 13), (*crossed_factors(), 739)]:
            report = check_labels(p, q, bound)
            n, d = p*q, report['d']
            self.assertEqual(d, 14 if n == 3599 else 1)
            s = 1+isqrt(d-1)
            limit = isqrt(n//s)
            roots = []
            for k, magnitude, denominator, _ in report['witnesses']:
                t, a = int(magnitude), int(denominator)
                self.assertEqual(t*t+d*a*a, k*n)
                self.assertTrue(1 <= k < 2*s and 1 <= a <= limit)
                self.assertLessEqual(t*(limit+1), n)
                self.assertEqual(gcd(a, n), 1)
                z = t*pow(a, -1, n) % n
                self.assertEqual(z*z % n, -d % n)
                roots.append(z)
            minus = gcd(roots[0]-roots[1], n)
            plus = gcd(roots[0]+roots[1], n)
            self.assertEqual({minus, plus}, {p, q})
            self.assertEqual(minus, int(report['divisor']))
