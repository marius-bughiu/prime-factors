from collections import Counter
import json
from math import gcd, prod
from pathlib import Path
import unittest

from experiments.affine_radix_holdout import draw_prime
from experiments.streamed_sum_join import search
from experiments.trace_folded_right import events, orbit_count


ROOT = Path(__file__).resolve().parents[1]


def shifted_menu(n, m, lower):
    return (m, {(v+n*pow(v, -1, m)-lower) % m for v in range(m) if gcd(v, m) == 1})


class FoldedRight(unittest.TestCase):
    def test_orbits_match_every_residue_including_fixed_points(self):
        for moduli in ((), (4,), (3, 5), (4, 3, 5)):
            period = prod(moduli)
            for lower in (0, 1, 4, 17):
                for n in (1, 5, 7, 11, 19):
                    groups = [shifted_menu(n, m, lower) for m in moduli]
                    residues = {t for t in range(period)
                                if all((t-lower) % m in values for m, values in groups)}
                    self.assertEqual(residues, {-t % period for t in residues})
                    fixed = sum(2*t % period == 0 for t in residues)
                    representatives = {min(t, -t % period) for t in residues}
                    self.assertEqual(orbit_count(groups, lower, len(residues)),
                                     (len(representatives), fixed))

    def test_events_agree_with_direct_sum_powers_through_wraps(self):
        n = 97
        for lower, width in ((0, 0), (7, 50), (330, 419), (848, 419)):
            left = [shifted_menu(n, m, lower) for m in (4, 5)]
            right = [shifted_menu(n, m, lower) for m in (3, 7)]
            period = 420
            for base in (1, 96, 22, 5):
                direct = sorted(s for s in range(lower, lower+width+1)
                                if all((s-lower) % m in values for m, values in left+right)
                                and pow(base, s, n) == pow(base, n+1, n))
                for reverse in (False, True):
                    work = Counter()
                    rows = list(events(n, base, lower, width, period, left, right,
                                       1000, reverse, work))
                    self.assertTrue(all(split is None for _, split in rows))
                    self.assertEqual(sorted(total for total, _ in rows), direct)
                    self.assertEqual(work['right_built'], work['right_orbits_visited'])

    def test_mixed_trace_separates_both_prime_factors(self):
        n = 372221
        opts = dict(candidates=(5,), max_right=3, max_visited=1)
        ordinary = search(n, **opts)
        folded = search(n, **opts, folded=True)
        self.assertEqual(ordinary['outcome'], 'left_limit')
        self.assertEqual(ordinary['work']['left_visited'], 1)
        self.assertEqual(folded['outcome'], 'trace_mixed_gcd')
        w = folded['work']
        self.assertEqual((w['left_visited'], w['square_tests'], w['trace_gcds']), (1, 0, 1))
        hit = w['trace_split']
        u, target, trace = (int(hit[key]) for key in ('u', 'target', 'trace'))
        self.assertNotIn(target, (u, pow(u, -1, n)))
        self.assertEqual((u+pow(u, -1, n)) % n, trace)
        self.assertEqual((target+pow(target, -1, n)) % n, trace)
        self.assertEqual((gcd(u-target, n), gcd(u*target-1, n)), (449, 829))
        self.assertEqual(folded['factors'], ['449', '829'])

    def test_predeclared_next_holdout_splits_with_half_storage(self):
        seed = b'streamed-sum-join-holdout-v1'
        factors = sorted(draw_prime(side, 1, bits=46, seed=seed) for side in (b'p', b'q'))
        n = prod(factors)
        self.assertEqual(n, 1880522624182833254908575971)
        opts = dict(candidates=(2,), max_visited=32256, reverse=True)
        self.assertEqual(search(n, **opts, max_right=20000)['outcome'], 'right_limit')
        folded = search(n, **opts, max_right=20000, folded=True)
        self.assertEqual(folded['factors'], list(map(str, factors)))
        self.assertEqual(folded['work']['left_visited'], 28022)
        self.assertEqual(folded['work']['right_built'], 17820)
        self.assertEqual(folded['work']['ordinary_right_potential'], 35640)
        stopped = search(n, **opts, max_right=17819, folded=True)
        self.assertEqual(stopped['outcome'], 'right_limit')
        for key in ('right_built', 'right_orbits_visited', 'left_visited', 'trace_matches'):
            self.assertEqual(stopped['work'][key], 0)

    def test_full_size_controls_stop_before_right_table(self):
        controls = json.loads((ROOT / 'benchmarks/trace-folded-right.json').read_text())
        for case in controls:
            if not case['id'].endswith('2048'):
                continue
            run = search(int(case['n']), candidates=(2,), folded=True, max_right=20000,
                         max_visited=32256, reverse=True)
            w = run['work']
            self.assertEqual(run['outcome'], 'right_limit')
            self.assertFalse(run['factors'])
            self.assertEqual(w['right_fixed_points'], 0)
            self.assertEqual(2*w['right_potential'], w['ordinary_right_potential'])
            self.assertGreaterEqual(w['right_potential'].bit_length(), 446)
            self.assertEqual((w['right_built'], w['right_orbits_visited'], w['left_visited']), (0, 0, 0))
