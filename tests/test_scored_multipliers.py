from fractions import Fraction
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from experiments import scored_multipliers as scored
from experiments.crt_holdout import draw_sample
from experiments.pell_relations import search as cf_search


class ScoredMultiplierTests(unittest.TestCase):
    def test_local_mean_from_projective_residues(self):
        n = 150235091
        for m in (1, 3, 7, 11, 15, 35):
            total = -Fraction(scored.log_weight(m), 2)
            for p in scored.PRIMES:
                depth = 3 if p == 2 else 2
                for j in range(1, depth+1):
                    modulus = p**j
                    roots = sum((x*x - m*n) % modulus == 0 for x in range(modulus))
                    probability = Fraction(roots, modulus + modulus//p)
                    # Beyond the last level each retained root's density falls geometrically.
                    tail = Fraction(p, p-1) if j == depth else 1
                    total += scored.log_weight(p) * probability * tail
            table = scored.score_table()
            signs = [n % p in sq for p, sq in zip(scored.PRIMES[1:], table.squares)]
            row = next(row for row in table.rows if row.multiplier == m)
            self.assertEqual(scored._score(n % 8, signs, row, table.dyadic),
                             total * table.denominator)

    def test_all_menu_scores_match_direct_euler_criterion(self):
        table = scored.score_table()
        self.assertEqual(table.profile, dict(odd_primes=24, squares_generated=517,
                                           multiplier_prime_pairs=624, unit_pairs=591,
                                           ramified_pairs=33))
        for n in range(3, 1024, 2):
            if any(n % p == 0 for p in scored.PRIMES[1:]):
                continue  # The public divisibility screen returns before candidate scoring.
            signs = [n % p in sq for p, sq in zip(scored.PRIMES[1:], table.squares)]
            for row in table.rows:
                m = row.multiplier
                d = m*n
                twos = {1: 4, 3: 1, 5: 2, 7: 1}[d % 8]
                direct = Fraction(twos*scored.log_weight(2),3) - Fraction(scored.log_weight(m),2)
                for p in scored.PRIMES[1:]:
                    if m % p == 0:
                        direct += Fraction(scored.log_weight(p), p+1)
                    elif pow(d, (p-1)//2, p) == 1:
                        direct += Fraction(2*p*scored.log_weight(p), p*p-1)
                self.assertEqual(direct*table.denominator,
                                 scored._score(n % 8, signs, row, table.dyadic))

    def test_support_and_setup(self):
        squarefree = tuple(i for i in range(1, 64, 2)
                           if all(i % (d*d) for d in range(2, 9)))
        self.assertEqual(scored.MULTIPLIERS, squarefree)
        self.assertEqual(scored.search(101**2, 'scored', 13)['factor'], 101)
        self.assertEqual(scored.search(3**3*101, 'scored', 13)['factor'], 3)
        self.assertEqual(scored.search(7, 'dyadic', 13)['outcome'], 'small_prime')
        self.assertEqual(scored.search(3*97, 'dyadic', 13)['outcome'], 'multiplier_gcd')
        self.assertEqual(scored.search(13, 'scored', 13)['outcome'], 'small_prime')
        with self.assertRaises(ValueError):
            scored.search(77, 'unknown', 13)
        with patch.object(scored, '_score', return_value=1):
            self.assertEqual(scored.search(101*109, 'scored', 0)['multiplier'], 1)

    def test_ordinary_walk_preserves_the_original_result(self):
        n = 21490481
        plain = cf_search(n, 1, 30)
        wrapped = scored.search(n, 'one', 30)
        self.assertEqual({k: wrapped[k] for k in plain}, plain)
        self.assertEqual(wrapped['residue_checks'], 0)
        self.assertEqual(wrapped['sign_comparisons'], 0)

    def test_saved_panel_has_the_predeclared_sample_and_replays_one_case(self):
        path = Path(__file__).resolve().parents[1] / 'research' / 'scored-holdout.json'
        data = json.loads(path.read_text())
        rows = data['cases']
        sample = list(draw_sample(b'crt-cf-score-v1', 64))
        self.assertEqual(len(rows), len(sample))
        for row, (attempt, n, known) in zip(rows, sample):
            self.assertEqual((row['attempt'],row['n'],row['expected_factors']),
                             (attempt,str(n),list(map(str,known))))
            for mode in scored.MODES:
                method = row['methods'][mode]
                if method['factors']:
                    self.assertEqual(method['factors'], row['expected_factors'])
                    self.assertEqual(method['remaining'], [])
                else:
                    self.assertEqual(method['remaining'], [row['n']])
        for mode in scored.MODES:
            w = scored.search(int(rows[0]['n']), mode, data['max_steps'])
            w.pop('factor')
            profile = w.pop('table_profile')
            if profile is not None:
                self.assertEqual(profile, data['table_profile'])
            w['selected_count'] = len(w.pop('selected_steps'))
            self.assertEqual(w, rows[0]['methods'][mode]['work'])
