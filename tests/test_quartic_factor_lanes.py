from collections import Counter
from itertools import product
from math import comb, gcd, isqrt, prod
import unittest
from unittest.mock import patch

from experiments.affine_radix_holdout import trial_search
from experiments.midpoint_weights import residue_pairs
from experiments.norm_auxiliary import integer_roots
from experiments.quartic_factor_lanes import (
    equation, lane_basis, parameters, search, signed_orbit_count, signed_representatives,
)


def taylor_coefficients(row, n, u):
    d, b, e, a, c = row
    coefficients = (d*n*n, b*n, e, a, c)
    return [sum(comb(k, j)*value*u**(k-j) for k, value in enumerate(coefficients) if k >= j)
            for j in range(5)]


def in_basis_span(row, basis):
    remaining = list(row)
    for j in reversed(range(5)):
        quotient, remainder = divmod(remaining[j], basis[j][j])
        if remainder:
            return False
        remaining = [x-quotient*y for x, y in zip(remaining, basis[j])]
    return remaining == [0]*5


class QuarticFactorLaneTests(unittest.TestCase):
    def test_triangular_lattice_is_exactly_the_four_taylor_congruences(self):
        for n, radix, u in ((15, 8, 1), (35, 6, 5), (91, 10, 3)):
            basis = lane_basis(n, u, radix)
            diagonals = [basis[j][j] for j in range(5)]
            self.assertEqual(diagonals, [radix**i for i in (4, 3, 2, 1, 0)])
            self.assertEqual(prod(diagonals), radix**10)
            self.assertTrue(all(basis[i][j] == 0 for i in range(5) for j in range(i+1, 5)))
            examples = list(product((-1, 0, 1), repeat=5))+basis
            examples.append([sum((i-2)*basis[i][j] for i in range(5)) for j in range(5)])
            for row in examples:
                coeffs = taylor_coefficients(row, n, u)
                satisfies = all(coeffs[i] % radix**(4-i) == 0 for i in range(4))
                self.assertEqual(in_basis_span(row, basis), satisfies)
                if satisfies:
                    for k in (-11, -1, 0, 1, 7):
                        self.assertEqual(sum(value*(radix*k)**i for i, value in enumerate(coeffs)) % radix**4, 0)

    def test_certificate_rejects_long_zero_and_noncongruent_vectors(self):
        for vector in ([0]*5, [0, 0, 4**4, 0, 0], [0, 0, 1, 0, 0]):
            with patch('experiments.quartic_factor_lanes.reduced_basis', return_value=([], [vector])):
                with self.assertRaises(ArithmeticError):
                    equation(3, 1, 4, 2, Counter())

    def test_lower_degree_eliminants_and_repeated_integer_roots(self):
        # n² R^(4-j) (X-u)^j gives a primitive eliminant k^j after shifting.
        n, u, radix = 3, 1, 256
        for degree in (1, 2, 3):
            coefficients = [n*n*radix**(4-degree)*comb(degree, i)*(-u)**(degree-i)
                            if i <= degree else 0 for i in range(5)]
            vector = [value//factor for value, factor in zip(coefficients, (n*n, n, 1, 1, 1))]
            with patch('experiments.quartic_factor_lanes.reduced_basis', return_value=([], [vector])):
                poly = equation(n, u, radix, 2, Counter())
            self.assertEqual(poly, [int(i == degree) for i in range(5)])
            self.assertEqual(integer_roots(poly, -5, 5), [0])
        # Both examples use the real reducer, including a quartic coefficient that vanishes.
        cubic = equation(173, 9, 14, 18, Counter())
        self.assertNotEqual(cubic[3], 0)
        self.assertEqual(cubic[4], 0)
        repeated = equation(3, 1, 4, 2, Counter())
        self.assertEqual(sorted(integer_roots(repeated, -4, 4)), [-1, 0])

    def test_product_identity_and_all_balanced_pairs(self):
        for n in (*range(3, 270, 2), 1225, 3465, 11025, 34387):
            bound, radix = parameters(n)
            self.assertEqual(bound, isqrt(2*n))
            self.assertGreaterEqual(radix**10, 6**5*bound**6)
            self.assertEqual(gcd(n, radix), 1)
            expected = trial_search(n)['pairs']
            result = search(n)
            self.assertEqual(result['pairs'], expected, n)
            self.assertEqual(result['remaining_orbits'], 0)
            for pair in expected:
                for x in map(int, pair):
                    u, k = x % radix, x//radix
                    poly = equation(n, u, radix, bound, Counter())
                    self.assertEqual(gcd(*poly), 1)
                    self.assertEqual(sum(c*k**j for j, c in enumerate(poly)), 0)
        self.assertEqual(search(1225)['pairs'], [['25', '49'], ['35', '35']])

    def test_negation_orbits_include_fixed_pairs_and_radix_one_and_two(self):
        for radix in range(1, 70):
            for n in (1, 3, 11, 35, 247):
                if gcd(n, radix) != 1:
                    continue
                count, reps = residue_pairs(n, radix, Counter())
                ordinary = {tuple(sorted(pair)) for pair in reps}
                fixed = {pair for pair in ordinary if tuple(sorted((-x) % radix for x in pair)) == pair}
                expected = (len(ordinary)+len(fixed))//2
                self.assertEqual(signed_orbit_count(n, radix, count, Counter()), expected)
                _, reps = residue_pairs(n, radix, Counter())
                chosen = {tuple(sorted(pair)) for pair in signed_representatives(reps, radix, Counter())}
                self.assertEqual(len(chosen), expected)
                self.assertEqual(chosen | {tuple(sorted((-u) % radix for u in pair)) for pair in chosen}, ordinary)
                self.assertTrue(fixed <= chosen)

    def test_signed_bands_recover_the_same_balanced_pairs(self):
        found_negative_root = False
        for n in (*range(3, 701, 2), 1225, 3465, 11025, 34387):
            ordinary, signed = search(n), search(n, signed=True)
            self.assertEqual(ordinary['pairs'], signed['pairs'])
            self.assertEqual(ordinary['total_orbits'], signed['ordinary_covered_orbits'])
            self.assertLessEqual(signed['work'].get('candidate_roots', 0), 4*signed['total_orbits'])
            if signed['pairs'] and signed['work'].get('negative_candidate_roots'):
                found_negative_root = True
        self.assertTrue(found_negative_root)
        fixed = search(247, signed=True)
        self.assertEqual(fixed['pairs'], [['13', '19']])
        self.assertEqual((fixed['ordinary_total_orbits'], fixed['total_orbits']), (4, 3))
        self.assertEqual(search(34387, power=3, signed=True)['pairs'], [['137', '251']])
        capped = search(3376036549, 2, signed=True)
        self.assertEqual(capped['visited_orbits'], 2)
        self.assertGreater(capped['remaining_orbits'], 0)
        self.assertLessEqual(capped['ordinary_covered_orbits'], 4)
        self.assertEqual(search(3376036549, 0, signed=True)['ordinary_covered_orbits'], 0)

    def test_zero_budget_and_partial_orbit_accounting(self):
        for cap in (0, 1, 3):
            run = search(3376036549, cap)
            self.assertEqual(run['visited_orbits'], cap)
            self.assertEqual(run['remaining_orbits'], run['total_orbits']-cap)
            self.assertEqual(run['work'].get('lll_calls', 0), cap)
        for n, cap in ((1, 0), (4, 2), (5, -1)):
            with self.assertRaises(ValueError):
                search(n, cap)
