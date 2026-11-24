"""Check the public direct sum, its one-word interface and its budget."""
import json
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from experiments import salie_seed as seed
from experiments.salie_reference import SCALE, cosine_bounds


class SalieSeedTests(unittest.TestCase):
    def test_product_only_fixtures(self):
        path = Path(__file__).resolve().parents[1] / 'benchmarks' / 'salie-seed.json'
        for case in json.loads(path.read_text()):
            n = int(case['n'])
            with self.subTest(n=n, budget=case['max_terms']):
                result = seed.search(n, case['max_terms'])
                for name, value in result.items():
                    if name != 'factor':
                        self.assertEqual(value, case[name], name)
                if case['factors']:
                    p, q = map(int, case['factors'])
                    self.assertEqual((result['factor'], p*q), (p, n))
                else:
                    self.assertIsNone(result['factor'])
                    self.assertEqual((result['sums'], result['certified_cells']), (0, 0))

    def test_direct_word_agrees_with_independent_four_root_formula(self):
        # Known reference roots are used only after the public sum is produced.
        # 221 exercises the real Gauss unit and the b=2 decoding branch.
        for n, root, branch in [(221, 118, 2), (667, 231, 1), (1763, 42, 1)]:
            with self.subTest(n=n):
                result = seed.search(n, n)
                frequency, word = result['seed_frequency'], result['seed_word']
                public = cosine_bounds(frequency, n)
                hidden = cosine_bounds(frequency*root, n)
                low, high = [2*(public[i]+hidden[i]) for i in range(2)]
                grid = SCALE >> result['seed_bits']
                self.assertLess((2*word-1)*grid, 2*low)
                self.assertLess(2*high, (2*word+1)*grid)
                with patch.object(seed, 'rounded_sum', side_effect=AssertionError):
                    replay = seed.decode_seed(n, word)
                self.assertEqual(replay['root'], root)
                self.assertEqual(replay['multiplier'], branch)
                for prime, residue in zip(seed.prime_schedule(n), replay['square_residues']):
                    a = branch*root % n
                    a = min(a, n-a)
                    self.assertEqual(residue, a*a % prime)

    def test_chebyshev_interval_contains_independent_rational_values(self):
        for degree in [1, 2, 3, 30, 105]:
            low, high = -SCALE//8, -SCALE//8 + (SCALE >> 32)
            enclosed = seed.chebyshev_bounds(low, high, degree)
            for numerator in (low, (low+high)//2, high):
                x = Fraction(numerator, SCALE)
                previous, current = Fraction(1), x
                for _ in range(1, degree):
                    previous, current = current, 2*x*current - previous
                self.assertLessEqual(enclosed[0], current*SCALE)
                self.assertLessEqual(current*SCALE, enclosed[1])

    def test_limits_and_schedule_gcd(self):
        self.assertEqual(seed.search(667, 0)['unit_gcds'], 0)
        self.assertEqual(seed.search(2**2048-1, 10)['outcome'], 'size_limit')
        self.assertEqual(seed.search(3*101, 0)['factor'], 3)
        with self.assertRaises(ValueError):
            seed.decode_seed(667, 1 << 90)
