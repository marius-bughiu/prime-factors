from collections import Counter
from fractions import Fraction
from math import isqrt
from random import Random
import unittest

from experiments.norm_auxiliary import (
    amplitudes, compare, ellipse_intersection, integer_roots, multiply, reduced_basis,
    scan, search, sector_count, sector_points, short_vector,
)


def determinant(rows):
    if len(rows) == 1:
        return rows[0][0]
    tail = rows[1:]
    return sum((-1)**i*v*determinant([r[:i]+r[i+1:] for r in tail])
               for i, v in enumerate(rows[0]))


def points_direct(total, d):
    points = []
    for v in range(1, isqrt((total-1)//d)+1):
        square = total-d*v*v
        t = isqrt(square)
        if t*t == square:
            points.append((t, v))
    return sorted(points)


class NormAuxiliaryTests(unittest.TestCase):
    def test_lll_lattice_and_reduction_against_rational_gram_schmidt(self):
        rng = Random(1713)
        for dimension in range(1, 6):
            for sample in range(12):
                rows = [[rng.randint(-5000, 5000) for _ in range(dimension)]
                        for _ in range(dimension)]
                if determinant(rows) == 0:
                    continue
                reduced, transform = reduced_basis(rows)
                self.assertEqual(abs(determinant(transform)), 1)
                for row, weights in zip(reduced, transform):
                    self.assertEqual(row, [sum(w*x for w, x in zip(weights, column))
                                           for column in zip(*rows)])
                orthogonal = []
                lengths = []
                for index, row in enumerate(reduced):
                    v = row[:]
                    for prev, length in zip(orthogonal, lengths):
                        mu = sum(x*y for x, y in zip(row, prev))/length
                        self.assertLessEqual(abs(mu), Fraction(1, 2))
                        v = [x-mu*y for x, y in zip(v, prev)]
                    norm = sum((x*x for x in v), Fraction())
                    if index:
                        self.assertLessEqual((Fraction(3, 4)-mu*mu)*lengths[-1], norm)
                    lengths.append(norm)
                    orthogonal.append(v)
                self.assertEqual(short_vector(rows), reduced[0])
        with self.assertRaises(ValueError):
            reduced_basis([[1, 1], [2, 2]])

    def test_root_isolation_repeated_roots_gaps_and_large_bounds(self):
        large = 2**256-177
        p = multiply(multiply([-large, 1], [-large, 1]), multiply([7, 1], [-2, 1]))
        w = Counter()
        self.assertEqual(integer_roots(p, -7, large, w), [-7, 2, large])
        self.assertLess(w['integer_root_nodes'], 8*large.bit_length())
        self.assertEqual(integer_roots([5, 0], -9, 9), [])
        with self.assertRaises(ValueError):
            integer_roots([0, 0], -9, 9)
        rng = Random(6541)
        for _ in range(70):
            p = [rng.randint(-30, 30) for _ in range(4)]+[1]
            expected = [x for x in range(-12, 14) if sum(c*x**i for i, c in enumerate(p)) == 0]
            self.assertEqual(integer_roots(p, -12, 13), expected)

    def test_resultant_checks_the_original_unsquared_equation(self):
        self.assertEqual(ellipse_intersection(65, 1, [-9, 1, 0, 1, 0], 1, 8),
                         [(1, 8), (8, 1)])
        self.assertEqual(ellipse_intersection(65, 1, [-9, 1, 0, -1, 0], 1, 8), [])
        # Both coefficients of the linear-in-y equation vanish at x=7.
        self.assertEqual(ellipse_intersection(65, 1, [0, 0, 0, -7, 1], 1, 8),
                         [(7, 4)])

    def test_complete_sectors_match_an_independent_coordinate_scan(self):
        for n in range(33, 146, 4):
            for d, k in ((1, 1), (2, 1), (5, 2), (14, 3)):
                total = n*k
                sectors = 1+n % 5
                result = search(n, d, k, sectors=sectors)
                with self.subTest(n=n, d=d, k=k):
                    self.assertTrue(result['interval_complete'])
                    self.assertEqual(sorted(result['points']), points_direct(total, d))
                    self.assertEqual(result['work']['coordinate_positions'], isqrt(total))
        self.assertEqual(search(5, 7)['points'], [])
        # The rational sector boundary z=1/2 contains (3,4) at total=25.
        work = Counter()
        amp = amplitudes(25, 1, 2)
        self.assertNotIn((3, 4), sector_points(25, 1, 2, 0, amp, work))
        self.assertIn((3, 4), sector_points(25, 1, 2, 1, amp, work))

    def test_public_split_and_shared_budget(self):
        n = 1009*1033
        w = {}
        self.assertEqual(list(scan(n, 1, 1, w, 0)), [])
        self.assertEqual((w['blocks'], w['outcome']), (0, 'block_limit'))
        result = compare(n, sectors=64)
        self.assertEqual(sorted(result['auxiliary']['points']), result['lines']['points'])
        self.assertEqual(len(result['lines']['points']), 4)
        self.assertIn(result['auxiliary']['factor'], (1009, 1033))
        self.assertEqual(result['auxiliary']['work']['blocks'], 64)
        self.assertEqual(result['lines']['work']['blocks'], 290)

    def test_translated_bases_keep_the_same_points_across_skipped_sectors(self):
        n = 1009*1033
        cold, warm = search(n), search(n, reuse_basis=True)
        self.assertEqual(warm['points'], cold['points'])
        self.assertEqual(warm['factor'], cold['factor'])
        w = warm['work']
        self.assertGreater(w['empty_coordinate_intervals'], 0)
        self.assertEqual(w['reused_bases']+1, w['lll_calls'])
        self.assertLess(w['lll_swaps'], cold['work']['lll_swaps'])

    def test_guaranteed_sector_count_has_at_most_one_candidate_level(self):
        for n, d in ((65, 1), (3599, 14), (11009, 2), (101*109, 1)):
            j = sector_count(n, d)
            self.assertLess(d*(j-1)**10, 8**10*n**3)
            self.assertLessEqual(8**10*n**3, d*j**10)
            a = amplitudes(n, d, j)
            for i in range(0, j, max(1, j//32)):
                w = Counter()
                sector_points(n, d, j, i, a, w)
                self.assertLessEqual(w['possible_levels'], 1)
