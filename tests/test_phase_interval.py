import json
import subprocess
import sys
import unittest
from itertools import combinations, product
from math import gcd
from pathlib import Path

from experiments import phase_interval, salie_blocks
from experiments.folded_square import produce
from experiments.salie_seed import rounded_sum


class PhaseIntervalTests(unittest.TestCase):
    def test_elementary_search_on_every_small_cube_radius_window(self):
        for n in range(15, 400, 2):
            radius = phase_interval.cube_radius(n)
            self.assertLessEqual(64*radius**3, n)
            self.assertGreater(64*(radius+1)**3, n)
            roots = {h for h in range(n) if h*h % n == 1 and 1 < gcd(h-1, n) < n}
            for start in range(0, n, 2*radius+1):
                end = min(n-1, start+2*radius)
                r = phase_interval.search_interval(n, start, end, 1)
                self.assertLessEqual(int(r['possible_lifts']), 1)
                self.assertEqual(r['factor'] is not None, any(start <= h <= end for h in roots))

    def test_blocked_enclosures_match_independent_direct_sums(self):
        for p, q, d in [(3, 5, 3), (5, 13, 7), (7, 11, 6), (23, 29, 5), (41, 43, 9)]:
            n = p*q
            counts = dict(unit_gcds=0, unit_inverses=0, jacobi_evaluations=0, terms=0, sums=0)
            direct = rounded_sum(n, 1, d, n, counts)
            run = salie_blocks.search(n, n, d)
            self.assertEqual(run['word'], direct)
            self.assertEqual(run['trig_calls'], 4)
            self.assertEqual(run['unit_terms'], (p-1)*(q-1))
            negative_roots = 4 if p % 4 == q % 4 == 1 else 0
            self.assertEqual(4*run['orbits'], run['unit_terms']+4+negative_roots)

    def test_budget_retains_divisors_found_in_membership_checks(self):
        one = salie_blocks.search(667, 1)
        self.assertEqual((one['factor'], one['word']), (None, None))
        short = salie_blocks.search(667, 154)
        self.assertEqual((short['factor'], short['word'], short['outcome']), (23, None, 'budget'))
        word = int(produce(23, 29, 5)[0]['word'])
        for lifts, blocks in [(0, 5), (5, 0)]:
            r = phase_interval.decode_word(667, word, 5, lifts, blocks)
            self.assertIsNone(r['factor'])
            self.assertEqual(r['square_tests'], 0)
        with self.assertRaises(ValueError):
            phase_interval.decode_word(667, 0, 11)

    def test_truncating_wide_cell_then_covering_all_blocks(self):
        n = 2027*2029
        word = int(produce(2027, 2029, 11)[0]['word'])
        short = phase_interval.decode_word(n, word, 11, 2, 1)
        full = phase_interval.decode_word(n, word, 11, 1000, 1000)
        self.assertGreater(short['blocks_needed'], 1)
        self.assertIsNone(short['factor'])
        self.assertEqual(full['factor'], 2027)
        self.assertTrue(all(int(row['possible_lifts']) <= 1 for row in full['intervals']))

    def test_one_coarse_word_on_crossed_certified_full_width_primes(self):
        families = ['continued-square', 'gap-stride', 'predecessor-square', 'reduced-orders', 'shifted']
        primes = []
        root = Path(__file__).resolve().parents[1] / 'benchmarks'
        for family in families:
            rows = json.loads((root / (family+'.json')).read_text())
            row = next(r for r in rows if int(r['n']).bit_length() == 2048 and len(r['factors']) == 2)
            primes.append(list(map(int, row['factors'])))
        products = set()
        steps = []
        for a, b in combinations(primes, 2):
            for p, q in product(a, b):
                n = p*q
                if n.bit_length() != 2048 or p == q:
                    continue
                products.add(n)
                payload, _ = produce(p, q, 1366)
                replay = phase_interval.decode_word(n, int(payload['word']), 1366)
                self.assertEqual(replay['factor'], min(p, q))
                self.assertEqual(replay['square_tests'], 1)
                steps.append(replay['intervals'][0]['euclidean_steps'])
        self.assertEqual(len(products), 32)
        self.assertEqual((min(steps), max(steps)), (28, 421))

    def test_isolated_full_size_replay(self):
        cmd = [sys.executable, phase_interval.__file__]
        emit = subprocess.run(cmd+['--emit', '1366'], capture_output=True, text=True, check=True)
        self.assertEqual(set(json.loads(emit.stdout)), {'n', 'word', 'fractional_bits'})
        result = subprocess.run(cmd+['--decode'], input=emit.stdout, capture_output=True, text=True, check=True)
        p = json.loads(result.stdout)['factor']
        n = int(json.loads(emit.stdout)['n'])
        self.assertTrue(1 < p < n and n % p == 0)
