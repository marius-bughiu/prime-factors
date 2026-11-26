from collections import Counter
import json
from math import gcd, isqrt
from pathlib import Path
import unittest

from experiments.affine_radix_holdout import draw_prime
from experiments.streamed_sum_join import _digits, _rows, search
from experiments.sum_signature_join import search as full_join

ROOT = Path(__file__).resolve().parents[1]
HOLDOUT = 2999205669099453866424720319
ARCHIVED = 216743551899887872400389319
MANY_MATCHES = 16000030340009399
MANY_BASE = 8392506781771267


class StreamedSumJoin(unittest.TestCase):
    def test_first_hash_draws(self):
        seed = b'streamed-sum-join-holdout-v1'
        pair = sorted(draw_prime(side, 0, bits=46, seed=seed) for side in (b'p', b'q'))
        self.assertEqual(pair, [45058864713217, 66561944873407])
        self.assertEqual(pair[0] * pair[1], HOLDOUT)
        self.assertEqual(gcd(pow(2, HOLDOUT-1, HOLDOUT)-1, HOLDOUT), 1)

    def test_wider_primality_budget_keeps_search_budget_separate(self):
        from scripts.factor import discover

        smaller, larger = 45058864713217, 66561944873407
        self.assertEqual(discover(HOLDOUT, 0, [smaller]), ([smaller], [larger], 0))
        self.assertEqual(discover(HOLDOUT, 0, [smaller], certificate_trial_limit=2_000_000),
                         ([smaller, larger], [], 0))
        self.assertEqual(discover(101*103, 0, [], certificate_trial_limit=2_000_000),
                         ([], [101*103], 0))
        with self.assertRaises(ValueError):
            discover(HOLDOUT, 0, [], certificate_trial_limit=0)

    def test_two_incorrect_sums_can_factor(self):
        run = search(MANY_MATCHES, candidates=(MANY_BASE,), max_right=65536, max_visited=65536)
        self.assertEqual(run['outcome'], 'gap_order_gcd')
        a, b = map(int, run['work']['first_two_sums'])
        self.assertNotEqual(a, b)
        for total in (a, b):
            self.assertEqual(pow(MANY_BASE, total, MANY_MATCHES),
                             pow(MANY_BASE, MANY_MATCHES+1, MANY_MATCHES))
            discriminant = total*total - 4*MANY_MATCHES
            self.assertNotEqual(isqrt(discriminant)**2, discriminant)
        self.assertEqual(pow(MANY_BASE, abs(a-b), MANY_MATCHES), 1)
        self.assertEqual(run['work']['square_tests'], 2)
        self.assertEqual(run['work']['left_entries_stored'], 0)
        self.assertEqual(run['factors'], ['100000039', '160000241'])

    def test_opposite_traversals_on_unique_matches(self):
        for n in (ARCHIVED, HOLDOUT):
            visits = []
            evidence = []
            for reverse in (False, True):
                run = search(n, candidates=(2,), max_right=65536,
                             max_visited=65536, reverse=reverse)
                work = run['work']
                self.assertEqual(run['outcome'], 'sum_square')
                self.assertEqual(work['square_tests'], 1)
                self.assertEqual(work['left_entries_stored'], 0)
                self.assertEqual(work['left_visited'] + work['left_unvisited'], work['left_potential'])
                visits.append(work['left_visited'])
                evidence.append(work['first_two_sums'])
            self.assertEqual(evidence[0], evidence[1])
            self.assertEqual(sum(visits), work['left_potential'] + 1)
            self.assertLessEqual(min(visits), (work['left_potential'] + 1)//2)

    def test_storage_and_visits_are_separate_caps(self):
        original = full_join(HOLDOUT, bases=[2], max_half_entries=40000)
        self.assertEqual(original['outcome'], 'half_list_limit')
        self.assertEqual(sorted((original['work']['left_entries'], original['work']['right_entries'])),
                         [37422, 64512])
        limited = search(HOLDOUT, candidates=(2,), max_right=37421, max_visited=1)
        self.assertEqual(limited['outcome'], 'right_limit')
        self.assertEqual(limited['work']['right_built'], 0)
        self.assertEqual(limited['work']['left_visited'], 0)
        run = search(HOLDOUT, candidates=(2,), max_right=40000, max_visited=1)
        self.assertEqual(run['outcome'], 'left_limit')
        self.assertEqual(run['work']['left_visited'], 1)
        self.assertEqual(run['work']['left_unvisited'], 64511)
        self.assertEqual(run['work']['right_built'], 37422)
        self.assertFalse(run['factors'])

    def test_preflight_without_list_construction(self):
        split = search(33127, candidates=(13,), max_right=1, max_visited=1)
        self.assertEqual(split['outcome'], 'preflight_gcd')
        self.assertEqual(split['factors'], ['157', '211'])
        unresolved = search(104653, candidates=(2, 3), max_right=1, max_visited=1)
        self.assertEqual(unresolved['outcome'], 'no_witness_within_cap')
        self.assertFalse(unresolved['factors'])
        for run in (split, unresolved):
            self.assertEqual(run['work'].get('left_visited', 0), 0)
            self.assertEqual(run['work'].get('right_built', 0), 0)

    def test_both_incremental_powers_across_wraps(self):
        n, base, period = 101, 2, 35
        groups = [(5, {0, 1, 4}), (7, {0, 3, 6})]
        inverse_period = pow(pow(base, period, n), -1, n)
        for subtract in (False, True):
            work = Counter()
            digits = _digits(groups, period, n, base, inverse_period, subtract, work)
            start = pow(base, 43, n) if subtract else 1
            forward = list(_rows(digits, period, n, start, work))
            reverse = list(_rows(digits, period, n, start, work, reverse=True))
            self.assertEqual(reverse, list(reversed(forward)))
            expected = {i for i in range(period) if i%5 in groups[0][1] and i%7 in groups[1][1]}
            self.assertEqual({i for i, signature in forward}, expected)
            for i, signature in forward:
                self.assertEqual(signature, pow(base, 43-i if subtract else i, n))

    def test_trial_cap_still_allows_later_true_sum_and_exhaustion(self):
        run = search(49998072529, candidates=(3,), gap_trial_cap=0)
        self.assertEqual(run['outcome'], 'sum_square')
        self.assertEqual(run['factors'], ['167329', '298801'])
        self.assertGreater(run['work']['gap_budget_stops'], 0)
        self.assertEqual(run['work']['trial_divisions'], 0)
        unbalanced = search(53*1009, candidates=(2,))
        self.assertEqual(unbalanced['outcome'], 'exhausted')
        self.assertEqual(unbalanced['work']['left_unvisited'], 0)
        self.assertEqual(unbalanced['factors'], [])

    def test_full_size_inputs_use_only_preflight_and_planning(self):
        controls = json.loads((ROOT / 'benchmarks/collision-gap-readout.json').read_text())
        for case in controls:
            if not case['id'].endswith('2048'):
                continue
            run = search(int(case['n']), candidates=(2,), max_right=40000, max_visited=32256)
            work = run['work']
            self.assertEqual(run['outcome'], 'right_limit')
            self.assertEqual(work['right_built'], 0)
            self.assertEqual(work['left_visited'], 0)
            self.assertEqual(work['left_unvisited'], work['left_potential'])
            self.assertFalse(run['factors'])
