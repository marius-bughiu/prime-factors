import json
import unittest
from math import gcd
from pathlib import Path
from unittest.mock import patch

from experiments import geometric_wheel_readout as wheel
from experiments.geometric_sum_readout import _interval


def absolute_products(n, base):
    """Check the actual lifted products using no normalization, grid, or inverse."""
    lower, upper = _interval(n, base, 0, 0)
    allowed = {(p + q) % 32 for p in range(1, 32, 2) for q in range(1, 32, 2)
               if (p*q - n) % 32 == 0}
    mod = n**3
    g = pow(base, n, mod)
    root = g * (1 + n) % mod
    target = pow(g, n + 1 - lower, mod)
    values = {str(z): 1 for z in (-1, 0, 1)}
    power = 1
    for i in range(upper - lower + 1):
        if (i + lower) % 32 in allowed:
            for key, current in values.items():
                values[key] = current * (target * (1 + int(key)*n) - power) % mod
        power = power * root % mod
    return values


class GeometricWheelReadout(unittest.TestCase):
    def test_every_odd_word_and_absolute_products(self):
        for n in list(range(306073, 306073 + 32, 2)) + [33127, 793157, 1599371087]:
            base = 2 if n != 793157 else 79
            run = wheel.search(n, base, 256, all_targets=True)
            self.assertEqual(run['samples'], absolute_products(n, base))
            self.assertEqual(sum(int(lane['count']) for lane in run['lanes']),
                             int(run['total_terms']))
            self.assertEqual(run['block_work']['root_polynomials'], int(int(run['common_length']) > 0))
            lengths = {int(lane['count']) for lane in run['lanes']}
            self.assertLessEqual(max(lengths) - min(lengths), 1)

    def test_transport_coefficients(self):
        for n, base in [(33127, 13), (793157, 79), (1599371087, 2)]:
            r = wheel.search(n, base, 256)
            constant, linear, quadratic = wheel.filtered_coefficients(
                n, r['reduced_base'], r['reduced_target'], int(r['origin']), int(r['dense_terms']))
            self.assertEqual(constant, r['constant'])
            self.assertEqual(linear, r['linear'])
            if r['quadratic'] is not None:
                self.assertEqual(quadratic, r['quadratic'])

    def test_two_filtered_hits_with_opposite_ranks(self):
        n, base = 793157, 79
        r = wheel.search(n, base, 2)
        self.assertEqual(r['outcome'], 'quotient_limit')
        self.assertIsNone(r['factor'])
        self.assertEqual(r['work']['quotient_gcds'], 48)
        self.assertEqual(r['quadratic'], [433771, 56478, 226366])
        lower, end = int(r['origin']), int(r['last_sum'])
        indices = [i for i in range(end-lower+1) if (i+lower) % 32 in r['accepted_mod_32']]
        for p, expected in [(727, [36, 80]), (1091, [16, 36])]:
            g, y = r['reduced_base'] % p, r['reduced_target'] % p
            self.assertEqual([i for i in indices if pow(g, i, p) == y], expected)
        index = 36
        self.assertEqual(lower + index, 727 + 1091)
        self.assertEqual((r['quadratic_A']*index**2 - r['quadratic_B']*index +
                          2*r['quadratic'][0]) % n, 0)
        self.assertEqual(gcd(r['quadratic_A'], n), 1)

    def test_budget_precedes_lifting_and_grid_construction(self):
        fixture = Path(__file__).resolve().parents[1] / 'benchmarks/geometric-wheel-readout.json'
        cases = json.loads(fixture.read_text())
        for case in cases:
            if not case['id'].endswith('2048'):
                continue
            with patch.object(wheel, 'pow', create=True, side_effect=AssertionError), \
                    patch.object(wheel, '_setup', side_effect=AssertionError):
                r = wheel.search(int(case['n']), case['base'], case['max_block_width'])
            self.assertEqual(r['outcome'], 'block_width_limit')
            self.assertEqual(r['work']['setup_powers'], 0)
            self.assertEqual(r['wheel_work']['step_powers'], 0)
            self.assertEqual(r['work']['unvisited_terms'], int(r['total_terms']))
            self.assertEqual(r['samples'], {})
            self.assertNotIn('block_work', r)

    def test_small_cases_and_tight_width(self):
        r = wheel.search(33127, 13, 0)
        self.assertEqual((r['factor'], r['winning_index']), (157, 3))
        self.assertEqual(r['block_work']['scalar_products'], 0)
        self.assertEqual(r['wheel_work']['extra_terms'], 6)
        r = wheel.search(1599371087, 2, 13)
        self.assertEqual((r['factor'],r['winning_index']), (34949,727))
        self.assertEqual(wheel.search(1599371087, 2, 12)['outcome'], 'block_width_limit')
        self.assertEqual(wheel.search(13, 2, 0)['outcome'], 'empty_filtered_interval')
        self.assertEqual(wheel.search(33127, 157, 0)['factor'], 157)
        with self.assertRaises(ValueError):
            wheel.search(33127, 13, -1)

    def test_reflected_optional_grid_does_not_change_products(self):
        n, base = 1599371087, 2
        r = wheel.search(n, base, 13, reflected=True, all_targets=True)
        self.assertEqual(r['samples'], absolute_products(n, base))
        self.assertEqual(r['factor'], 34949)
