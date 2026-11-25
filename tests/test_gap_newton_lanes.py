from collections import Counter
import json
from math import factorial, isqrt, prod
from pathlib import Path
import unittest
from unittest.mock import patch

from experiments.affine_radix_holdout import trial_search
from experiments.gap_newton_lanes import dickson_basis, equation, gap_coordinates, gap_monomials
from experiments.gap_newton_lanes import gap_scales, minimum_radix, search
from experiments.newton_lanes import coprime_factorials


class GapNewtonTests(unittest.TestCase):
    def test_integral_change_of_coordinates_and_signed_bounds(self):
        for power in (1, 2, 3, 4):
            dim = 2*power+1
            for x,y in ((9, 9), (5, 9), (9, 5), (-7, -13), (-13, -7)):
                n, diff = x*y, x-y
                transform = gap_monomials(n, power)
                monomials = [y**max(power-j, 0)*x**max(j-power, 0) for j in range(dim)]
                gap_values = [1]+[v for j in range(1, power+1) for v in (diff**j, x*diff**(j-1))]
                scales = gap_scales(n, power)
                self.assertEqual(gap_values, [sum(a*b for a,b in zip(row,monomials)) for row in transform])
                self.assertTrue(all(abs(a) <= b for a,b in zip(gap_values, scales)))
                for i in range(dim):
                    original = [int(i == j) for j in range(dim)]
                    gap = gap_coordinates(original, transform)
                    self.assertEqual(original, [sum(a*row[j] for a,row in zip(gap,transform)) for j in range(dim)])
                factorials = coprime_factorials(n, 2*power)
                target = minimum_radix(prod(scales), factorials)
                rhs = dim**dim * 2**(power*dim) * prod(scales)**2
                exponent = 2*power*dim
                self.assertLessEqual((target-1)**exponent * prod(factorials)**2, rhs)
                self.assertGreater(target**exponent * prod(factorials)**2, rhs)

    def test_direct_root_and_complete_search(self):
        x,y = -149,-293
        n, power = x*y, 2
        scales = gap_scales(n, power)
        factorials = [factorial(j) for j in range(2*power+1)]
        radix = minimum_radix(prod(scales), factorials)
        u, k = x%radix, x//radix
        polynomial = equation(n, u, radix, power, factorials, gap_monomials(n, power), scales, Counter())
        self.assertTrue(any(polynomial))
        self.assertEqual(sum(c*k**j for j,c in enumerate(polynomial)), 0)
        wrong_vectors = ([[0]*5], [[0, 0, 1, 0, 0]])
        with patch('experiments.gap_newton_lanes.reduced_basis', return_value=wrong_vectors):
            with self.assertRaisesRegex(ArithmeticError, 'absolute gap trace bound'):
                equation(n, u, radix, power, factorials, gap_monomials(n, power), scales, Counter())
        for n in (*range(3, 151, 2), 1225, 3465, 11025, 43657):
            run = search(n)
            self.assertEqual(run['pairs'], trial_search(n)['pairs'])
            self.assertEqual(run['remaining_orbits'], 0)
            self.assertEqual(run['ordinary_total_orbits'], run['ordinary_covered_orbits'])

    def test_dickson_transform_and_integer_weights(self):
        power = 4
        for x,y in ((3,3), (5,9), (9,5), (-5,-9), (-9,-5)):
            n, gap = x*y, x-y
            s = max(1, isqrt(n//8))
            basis, scales = dickson_basis(n, power)
            previous, current = 2, gap
            expected = [1]
            for j in range(1, power+1):
                expected.extend((current, x*(1 if j == 1 else previous)))
                previous, current = current, gap*current-s*s*previous
            values = [y**max(power-j,0)*x**max(j-power,0) for j in range(2*power+1)]
            self.assertEqual(expected, [sum(c*v for c,v in zip(row,values)) for row in basis])
            self.assertTrue(all(abs(v) <= w for v,w in zip(expected,scales)))
            for i,row in enumerate(basis):
                self.assertEqual(gap_coordinates(row, basis), [int(i == j) for j in range(len(row))])
        for n in (3, 9, 15, 35, 1225, 3465, 11025, 43657):
            self.assertEqual(search(n, power=3, basis='dickson')['pairs'], trial_search(n)['pairs'])

    def test_stored_control_setup(self):
        directory = Path(__file__).resolve().parents[1]/'research'
        control = json.loads((directory/'gap-newton-lanes.json').read_text())['capped_2048']
        n = int(json.loads((directory/'certified-control.json').read_text())['product'])
        self.assertEqual(control['n'], str(n))
        self.assertEqual(control['remaining_cofactor'], str(n))
        for basis in ('gap', 'dickson'):
            run = search(n, 0, basis=basis)
            recorded = control['methods'][basis]
            self.assertEqual((run['radix'],run['total_orbits']), (recorded['radix'],recorded['total_orbits']))
            self.assertEqual(recorded['remaining_orbits'], run['total_orbits']-control['max_orbits'])
            self.assertEqual(recorded['pairs'], [])
