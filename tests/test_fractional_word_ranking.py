import json
from collections import Counter, defaultdict
from itertools import combinations
from math import isqrt
from pathlib import Path
import random
import unittest
from unittest.mock import patch

from experiments import fractional_word_ranking as fractional
from experiments import high_word_suffix_ranking as exact


class FractionalWordRankingTests(unittest.TestCase):
    def test_bounds_cover_small_inputs_and_full_width_bin_edges(self):
        for k in (8, 12):
            table = fractional.root_table(k)
            for n in range(1 << 15):
                low, high, reads = table.bracket(n)
                self.assertLessEqual(low, isqrt(n))
                self.assertLessEqual(isqrt(n), high)
                if n < 1 << k:
                    self.assertEqual((low, high, reads), (isqrt(n), isqrt(n), 1))
            rng = random.Random(917633)
            for _ in range(64):
                n = (1 << 2047) | rng.getrandbits(2047)
                shift = (n.bit_length() - k + 1) // 2
                bin_width = 1 << (2 * shift)
                start = (n // bin_width) * bin_width
                for x in (n, start - 1, start, start + bin_width - 1, start + bin_width):
                    low, high, reads = table.bracket(x)
                    self.assertLessEqual(low, isqrt(x))
                    self.assertLessEqual(isqrt(x), high)
                    self.assertEqual(reads, 2)
            # If the next index is a perfect square the integer below its scaled root
            # is the last possible answer, including at the right edge of the bin.
            index = (1 << (k // 2)) ** 2 - 1
            x = ((index + 1) << 20) - 1
            self.assertEqual(table.bracket(x)[1], isqrt(x))

    def test_first_tied_winner_and_empty_class_against_odd_pairs(self):
        bits, word, modulus = 10, 519, 24
        base = 1 << bits
        first = isqrt((word + 1) * base - 1)
        rows = defaultdict(Counter)
        for p, q in combinations(range(base // 2 + 1, base, 2), 2):
            n, midpoint = p * q, (p + q) // 2
            if n >> bits == word and first <= midpoint <= first + modulus:
                rows[n % modulus][midpoint] += 1
        self.assertFalse(rows[13])
        self.assertGreater(list(rows[15].values()).count(max(rows[15].values())), 1)
        for residue in range(modulus):
            counts = rows[residue]
            winner = min(counts, key=lambda u: (-counts[u], u), default=None)
            for k in (8, 12):
                with self.subTest(residue=residue, k=k):
                    work = fractional.propose(bits, word, modulus, residue, k)
                    self.assertEqual(work['midpoint'], winner)
                    self.assertEqual(work['setup_roots'], 1 + work['refinement_roots'])

    def test_66_bit_cases_and_full_width_controls(self):
        fixtures = Path(__file__).resolve().parents[1] / 'benchmarks/high-word-suffix-ranking.json'
        cases = {case['id']: case for case in json.loads(fixtures.read_text())}
        for case_id in ('word-suffix-ranked-gain', 'word-suffix-ranked-misses',
                        'word-suffix-ranked-fresh-2048', 'word-suffix-ranked-crossed-2048'):
            case = cases[case_id]
            n, bits, modulus = int(case['n']), case['factor_bits'], case['modulus']
            reference, original = exact.search(n, bits, modulus)
            for k in (8, 12):
                with self.subTest(case=case['id'], k=k):
                    factor, work = fractional.search(n, bits, modulus, k)
                    self.assertEqual((factor, work['midpoint']), (reference, original['midpoint']))
                    self.assertEqual(work['square_tests'], 1)
                    self.assertEqual(work['refinement_roots'], 4 if bits == 33 and k == 8 else 0)
                    self.assertEqual(work['setup_roots'], 1 + work['refinement_roots'])
                    self.assertEqual(work['table_lookups'], 2 * work['root_brackets'])
                    self.assertEqual(work['root_table_entries'], (1 << k) + 1)
                    direct, direct_work = exact.scan_fermat(n, modulus, work['setup_roots'])
                    if case['id'] == 'word-suffix-ranked-gain':
                        self.assertEqual(factor, 6073583363)
                        self.assertEqual(direct, factor if k == 8 else None)
                        self.assertEqual(direct_work['square_tests'], 2 if k == 8 else 1)
                    elif case['id'] == 'word-suffix-ranked-misses':
                        self.assertIsNone(factor)
                        self.assertEqual(direct, 6073682449)
                    else:
                        self.assertIsNone(factor)
                        self.assertIsNone(direct)

    def test_count_separates_table_precomputation_and_exact_refinements(self):
        fractional.root_table.cache_clear()
        with patch.object(fractional, 'isqrt', wraps=isqrt) as lookup_root:
            fractional.root_table(8)
            self.assertEqual(lookup_root.call_count, 257)
            with patch('experiments.high_word_sum_ranking.isqrt', wraps=isqrt) as exact_root:
                # The outer bracket admits a candidate here, but refinement eliminates it.
                empty = fractional.propose(8, 128, 120, 7, 8)
                self.assertIsNone(empty['midpoint'])
                self.assertEqual(exact_root.call_count, empty['refinement_roots'])
                self.assertEqual(empty['refinement_roots'], 2)
                exact_root.reset_mock()
                _, work = fractional.search(36893488155787837121, 33, 120, 8)
                self.assertEqual(exact_root.call_count, work['refinement_roots'] + work['square_tests'])
            self.assertEqual(lookup_root.call_count, 257 + 2)

    def test_eight_bit_equal_root_budget_with_actual_direct_scans(self):
        primes = [p for p in range(129, 256, 2) if all(p % d for d in range(3, isqrt(p) + 1, 2))]
        for modulus in (24, 120):
            for panel in fractional.census(8, modulus):
                k = panel['precision']
                observed = Counter()
                for p, q in combinations(primes, 2):
                    n = p * q
                    if n.bit_length() != 16:
                        continue
                    got, work = fractional.search(n, 8, modulus, k)
                    budget = work['setup_roots'] + work['square_tests'] - 1
                    direct, costs = exact.scan_fermat(n, modulus, budget)
                    self.assertIn(got, (None, p))
                    self.assertIn(direct, (None, p))
                    observed.update(pairs=1, ranked=got == p, direct=direct == p,
                                    ranked_only=got == p and direct is None,
                                    direct_only=got is None and direct == p,
                                    direct_square_tests=costs['square_tests'])
                self.assertEqual(observed['pairs'], 148)
                self.assertEqual(observed, {key: panel['per_product'][key] for key in observed})
