"""Check the benchmark witness against the original translated cubic moments."""
from math import gcd
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from experiments.hasse_hankel_probe import search
from scripts.benchmark import run_case


def determinant(rows):
    if not rows:
        return 1
    return sum((-1)**i * x * determinant([row[:i]+row[i+1:] for row in rows[1:]])
               for i, x in enumerate(rows[0]))


class HankelProbeTest(unittest.TestCase):
    def test_witness_from_original_moments(self):
        n, c = 111281, 334
        cubic = (c**3-c, 3*c*c-1, 3*c, 1)
        power = [1]
        moments = [1]
        for m in range(1, 13):
            next_power = [0]*(len(power)+3)
            for i, a in enumerate(power):
                for j, b in enumerate(cubic):
                    next_power[i+j] += a*b
            power = next_power
            moments.append(power[2*m])
        hankel = [determinant([moments[i:i+k] for i in range(k)]) for k in range(8)]
        equations = [[hankel[j+1]*hankel[j+3], hankel[j+2]**2, hankel[j]*hankel[j+4]]
                     for j in range(4)]
        values = [gcd(n, determinant(equations[j:j+3])) for j in (0, 1)]
        self.assertEqual(values, [257, 1])
        self.assertEqual(search(n)['rows'][-1]['raw'], values)

    def test_comparison_split_does_not_complete_the_benchmark(self):
        self.assertIn(17, search(493)['descending_odd'])
        case = dict(id='hankel-comparison-only', description='Comparison-only hit', n='493',
                    status='partial', factors=[], remaining=['493'], shifts_checked=4, raw_gcds=8,
                    comparison_gcds=32, first_shift=None, first_start=None, raw_values=['1']*8)
        with TemporaryDirectory() as dirname:
            run = run_case(case, 'hasse-hankel-probe', Path(dirname))
            self.assertEqual(run['remaining'], ['493'])
            self.assertIsNone(run['certificate'])
            self.assertFalse(list(Path(dirname).iterdir()))
