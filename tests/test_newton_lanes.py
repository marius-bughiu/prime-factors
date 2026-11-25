from collections import Counter
from itertools import product
import json
from math import factorial, gcd, prod
import unittest
from unittest.mock import patch

from experiments.affine_radix_holdout import ROOT, trial_search
from experiments.newton_lanes import coprime_factorials, radix_threshold, vanishes_on_grid
from experiments.quartic_factor_lanes import equation, lane_basis, search


def in_lattice(vector, rows):
    residual = list(vector)
    for j in reversed(range(len(rows))):
        multiple, remainder = divmod(residual[j], rows[j][j])
        if remainder:
            return False
        residual = [x - multiple*y for x, y in zip(residual, rows[j])]
    return not any(residual)


class NewtonLaneTests(unittest.TestCase):
    def test_nonunit_factorials_and_strict_radix_rounding(self):
        for n in (1, 3, 9, 15, 35, 105, 143):
            factors = coprime_factorials(n, 12)
            for j, value in enumerate(factors):
                self.assertEqual(gcd(n, value), 1)
                leftover, rem = divmod(factorial(j), value)
                self.assertEqual(rem, 0)
                # Every prime dividing what was removed has to divide n.
                for p in (2, 3, 5, 7, 11):
                    if leftover % p == 0:
                        self.assertEqual(n % p, 0)
            for t in (1, 2, 3):
                dim = 2*t+1
                for bound in (1, 2, 5, 63, 64, 65, (1 << 1024)-1):
                    rhs = dim**dim * 2**(t*dim) * bound**(2*t*(t+1))
                    for contents in (factors[:dim], [1]*dim):
                        radix = radix_threshold(bound, t, contents)
                        margin = prod(contents)**2
                        self.assertLessEqual((radix-1)**(2*t*dim)*margin, rhs)
                        self.assertGreater(radix**(2*t*dim)*margin, rhs)

    def test_basis_index_and_membership_by_direct_evaluation(self):
        for n, r, u, t in ((15, 8, 1, 2), (35, 6, 5, 2), (77, 1, 0, 2),
                            (143, 5, 2, 3), (315, 4, 1, 3)):
            d, m = 2*t, 2*t+1
            contents = coprime_factorials(n, d)
            modulus = r**d * contents[-1]
            basis = lane_basis(n, u, r, t, contents)
            diagonals = [row[j] for j, row in enumerate(basis)]
            self.assertEqual(diagonals, [modulus//(r**j * contents[j]) for j in range(m)])
            self.assertEqual(prod(diagonals)*r**(t*m)*prod(contents), modulus**m)
            vectors = list(product((-1, 0, 1), repeat=m)) + basis
            vectors.extend([[sum((i-shift)*basis[i][j] for i in range(m)) for j in range(m)]
                            for shift in (0, t, d)])
            points = [u + r*k for k in range(-d, d+1)]
            weights = [n**max(t-j, 0) for j in range(m)]
            for c in vectors:
                values = [sum(a*w*x**j for j, (a, w) in enumerate(zip(c, weights))) for x in points]
                self.assertEqual(in_lattice(c, basis), all(y % modulus == 0 for y in values))

    def test_integer_values_can_vanish_without_coefficientwise_divisibility(self):
        # (k)_4 is always a multiple of 4!, including at negative k.
        shifted = [0, -6, 11, -6, 1]
        self.assertTrue(vanishes_on_grid(shifted, 24))
        self.assertFalse(all(c % 24 == 0 for c in shifted))
        self.assertFalse(vanishes_on_grid([0, -6, 11, -6, 2], 24))
        n, u, r = 35, 1, 64
        contents = coprime_factorials(n, 4)
        # A scalar multiple of the degree-one basis polynomial, returning k.
        vector = [-u*r**3*contents[-1], n*r**3*contents[-1], 0, 0, 0]
        with patch('experiments.quartic_factor_lanes.reduced_basis', return_value=([], [vector])):
            self.assertEqual(equation(n, u, r, 1, Counter(), 2, contents), [0, 1, 0, 0, 0])
        for bad in ([0]*5, [0, 0, r**4*contents[-1], 0, 0], [0, 0, 1, 0, 0]):
            with patch('experiments.quartic_factor_lanes.reduced_basis', return_value=([], [bad])):
                with self.assertRaises(ArithmeticError):
                    equation(n, u, r, 1, Counter(), 2, contents)

    def test_complete_search_on_squares_nonunits_and_multiple_pairs(self):
        for n in (*range(3, 201, 2), 1225, 3465, 11025, 34387):
            expected = trial_search(n)['pairs']
            for basis in ('taylor-exact', 'newton'):
                run = search(n, signed=True, basis=basis)
                self.assertEqual(run['pairs'], expected)
                self.assertEqual(run['remaining_orbits'], 0)
                self.assertEqual(run['ordinary_total_orbits'], run['ordinary_covered_orbits'])
                self.assertGreaterEqual(run['radix'], run['minimum_radix'])
        for power in (1, 3):
            for n in (3, 9, 15, 105, 1225):
                self.assertEqual(search(n, signed=True, basis='newton', power=power)['pairs'],
                                 trial_search(n)['pairs'])
        # With enough factorial content even stride one is a valid Newton lane.
        whole = search(11, signed=True, basis='newton', power=7)
        self.assertEqual((whole['radix'], whole['total_orbits'], whole['remaining_orbits']), (1, 1, 0))

    def test_full_size_prefix_accounting(self):
        frozen = json.loads((ROOT/'research/newton-lane-holdout.json').read_text())['capped_2048']
        n = int(frozen['n'])
        self.assertEqual(n.bit_length(), 2048)
        self.assertEqual(frozen['remaining_cofactor'], str(n))
        for basis, prefix in frozen['methods'].items():
            setup = search(n, 0, basis=basis, signed=True)
            self.assertEqual((setup['radix'], setup['total_orbits']), (prefix['radix'], prefix['total_orbits']))
            self.assertEqual(prefix['visited_orbits'], frozen['max_orbits'])
            self.assertEqual(prefix['remaining_orbits'], setup['total_orbits']-frozen['max_orbits'])
            self.assertEqual(prefix['work']['lll_calls'], frozen['max_orbits'])
            self.assertFalse(prefix['pairs'])
