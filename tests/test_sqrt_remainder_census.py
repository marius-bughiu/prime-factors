import json
from itertools import combinations
from math import isqrt
from pathlib import Path
import unittest

from experiments import sqrt_remainder_census as census
from experiments.affine_radix_holdout import draw_prime as trial_draw_prime
from experiments.factor_sum_quantile import sum_bounds


class SquareRootRemainderCensusTests(unittest.TestCase):
    def test_bit_at_shell_endpoints_and_half_threshold(self):
        for r in range(100):
            for n in range(r * r, (r + 1)**2):
                self.assertEqual(census.high_remainder(n), 4 * n > (2 * r + 1)**2)

    def test_small_exhaustive_panels_against_factor_sum_cut(self):
        archive = Path(__file__).resolve().parents[1] / 'research/sqrt-remainder-census.json'
        published = json.loads(archive.read_text())['exhaustive']
        for row in published[:5]:
            bits = row['factor_bits']
            primes = [p for p in range(1 << (bits - 1), 1 << bits)
                      if all(p % d for d in range(2, isqrt(p) + 1))]
            counts = [0] * 4
            for p, q in combinations(primes, 2):
                n = p * q
                if n.bit_length() != 2 * bits:
                    continue
                _, central, _ = sum_bounds(n, bits)
                high = 4 * n > (2 * isqrt(n) + 1)**2
                counts[2 * high + (p + q <= central)] += 1
            self.assertEqual(row['counts'], counts)
            self.assertEqual(census.exhaustive(bits), row)

    def test_seeded_draw_matches_reference_trial_division(self):
        counts = [0] * 4
        index = 0
        while sum(counts) < 16:
            pair = [trial_draw_prime(side, index, bits=32, seed=census.SEED)
                    for side in (b'p', b'q')]
            self.assertEqual(pair, [census.draw_prime(side, index) for side in (b'p', b'q')])
            index += 1
            p, q = sorted(pair)
            n = p * q
            if p == q or n.bit_length() != 64:
                continue
            _, central, _ = sum_bounds(n, 32)
            counts[2 * census.high_remainder(n) + (p + q <= central)] += 1
        row = census.fresh_panel(16)
        self.assertEqual((row['counts'], row['draw_indices']), (counts, index))
