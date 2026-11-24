import unittest

from experiments.gap_coverage import primes_through
from experiments.polynomial_relations import analyze, lifted_root, local_roots_table, search, sieve
from experiments.rational_squares import prime_parity


class PolynomialRelationTests(unittest.TestCase):
    def test_exact_sieve_including_ramified_coefficients(self):
        n, radius = 277*281, 44
        primes = [p for p in primes_through(17) if local_roots_table(p)[n % p]]
        base = [(1 << (i+1), p, local_roots_table(p)[n % p]) for i,p in enumerate(primes)]
        for a in (1, 49, 121):
            roots = [b for b in range(a) if (b*b-n) % a == 0]
            self.assertTrue(roots)
            for b in roots:
                work = dict(sieve_progressions=0, sieve_marks=0, prime_divisions=0)
                actual = sieve(n, a, b, radius, base, work)
                expected, marks, divisions = [], 0, 0
                for x in range(-radius, radius+1):
                    y = ((a*x+b)**2-n)//a
                    left = abs(y)
                    for p in primes:
                        marks += int(left % p == 0)
                        while left % p == 0:
                            left //= p
                            divisions += 1
                    if left == 1:
                        expected.append((x, y, prime_parity(y,primes)))
                self.assertEqual(actual, expected)
                self.assertEqual((work['sieve_marks'],work['prime_divisions']), (marks,divisions))

    def test_same_rows_admit_triangle_only_with_shared_prime_labels(self):
        rows = [(1,31*61,1), (2,61*151,1), (3,151*31,4)]
        metadata = [(0,0,0,(0,1)), (0,1,1,(1,2)), (0,2,2,(0,2))]
        full = analyze(15, rows, metadata, 1, 'edges')
        self.assertEqual((full['dependencies'], full['factor'], full['odd_coefficients']), (1,3,3))
        for mode in ('coefficient', 'polynomial'):
            self.assertEqual(analyze(15, rows, metadata, 1, mode)['dependencies'], 0)
        # Two sign choices of one coefficient can cancel without creating a graph cycle.
        duplicated = [(1,31*61,1), (2,31*61,4)]
        shared = [(0,0,0,(0,1)), (0,1,0,(0,1))]
        self.assertEqual(analyze(15, duplicated, shared, 1, 'coefficient')['factor'], 3)
        self.assertEqual(analyze(15, duplicated, shared, 1, 'polynomial')['dependencies'], 0)

    def test_unit_root_lift_and_search_controls(self):
        for n in (16, 22, 91):
            root = lifted_root(n,3,1,3**41)
            self.assertEqual((root*root-n) % (3**41), 0)
        self.assertEqual(search(121, 'square')['factor'], 11)
        self.assertEqual(search(143, 'edges', bound=11)['factor'], 11)
        with self.assertRaises(ValueError):
            search(77,'other')
        control = search(277*281, 'edges', bound=17, radius=4, blocks=2)
        self.assertEqual((control['blocks'],control['positions']), (2,18))
        for policy in control['policies'].values():
            if policy['factor']:
                self.assertIn(policy['factor'],(277,281))
