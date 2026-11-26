import json
from math import isqrt
from pathlib import Path
import unittest

from experiments.cubic_forced_units import diagonal
from experiments.cubic_gap_window import search


class CubicGapWindowTests(unittest.TestCase):
    def test_rounded_midpoint_on_small_products(self):
        for n in range(3, 513, 2):
            result = search(n)
            g = int(result['half_gap_estimate'])
            self.assertLess((g-2)**3, 4*n)
            self.assertLessEqual(4*n, (g-1)**3)
            x = n+g*g
            low = isqrt(x)
            self.assertEqual(int(result['midpoint']), low if x <= low*low+low else low+1)
            if result['factors']:
                p, q = map(int, result['factors'])
                self.assertGreater(p, 1)
                self.assertEqual(p*q, n)
            else:
                self.assertEqual(result['unresolved'], str(n))

    def test_recovers_pair_outside_the_exact_shape(self):
        case = json.loads((Path(__file__).resolve().parents[1]/'research/cubic-gap-control.json').read_text())
        n = int(case['product'])
        result = search(n)
        self.assertEqual(result['factors'], case['factors'])
        self.assertEqual(result['factor_candidates'], 1)
        self.assertEqual(abs(int(case['half_gap_error'])).bit_length(), 338)
        self.assertEqual(diagonal(n)['factors'], [])
