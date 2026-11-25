"""Compare three-row coefficient determinants and four-row minors on bounded quartic windows."""

import argparse
from collections import Counter
from itertools import combinations
import json
from math import gcd
from pathlib import Path
from time import process_time

from .quartic_basis_translation import reduce_window, window_layout


def high_minor(rows, indices):
    """The determinant of coefficient columns x², x³ and x⁴ of three rows."""
    (a, b, c), (d, e, f), (g, h, i) = [rows[index][2:] for index in indices]
    return a * (e*i - f*h) - b * (d*i - f*g) + c * (d*h - e*g)


def search(n, *, schedule, blocks):
    """Report every proper three-row gcd and compare all five four-row gcds."""
    if schedule not in ('midpoint', 'full', 'quartile') or blocks is None or blocks < 0:
        raise ValueError('expected a named schedule and an explicit nonnegative block cap')
    start = process_time()
    layout = window_layout(n, full=(schedule != 'quartile'), blocks=blocks)
    radius, first = layout['radius'], layout['first_center']
    total, visited = layout['total_blocks'], layout['visited_blocks']
    prefix, suffix = layout['unvisited_prefix_blocks'], layout['unvisited_suffix_blocks']
    if schedule == 'midpoint':
        # Place every odd integer in the public equal-width range in one window.
        count = (layout['last_odd'] - layout['first_odd']) // 2 + 1
        radius = max(1, count // 2)
        first = layout['first_odd'] + 2 * (count // 2)
        total, visited = 1, min(1, blocks)
        prefix, suffix = 0, total - visited
    counters = ('lll_calls', 'lll_swaps', 'lll_reductions', 'translations', 'triples_tested',
                'short_triples', 'zero_minors', 'whole_n_strips', 'minor_gcds', 'unit_gcds',
                'whole_modulus_gcds', 'proper_gcds', 'short_proper_gcds', 'hit_windows',
                'four_row_gcds', 'four_row_proper_gcds', 'integer_root_nodes')
    work = Counter(dict.fromkeys(counters, 0))
    previous, dual = None, []
    scale = [radius**i for i in range(5)]
    hits = []
    for block in range(visited):
        center = first + 2 * block * (2*radius + 1)
        previous, _, short = reduce_window(n, center, radius, scale, previous, work,
                                           dual_coordinates=dual)
        work['four_row_gcds'] += len(dual)
        work['four_row_proper_gcds'] += sum(1 < gcd(v, n) < n for v in dual)
        before = len(hits)
        for indices in combinations(range(5), 3):
            work['triples_tested'] += 1
            all_short = all(i in short for i in indices)
            work['short_triples'] += int(all_short)
            determinant = high_minor(previous, indices)
            if not determinant:
                work['zero_minors'] += 1
                continue
            reduced = abs(determinant)
            while reduced % n == 0:
                reduced //= n
                work['whole_n_strips'] += 1
            common = gcd(n, reduced)
            work['minor_gcds'] += 1
            if common == 1:
                work['unit_gcds'] += 1
            elif common == n:
                work['whole_modulus_gcds'] += 1
            else:
                work['proper_gcds'] += 1
                work['short_proper_gcds'] += int(all_short)
                hits.append(dict(block=block, center=center, rank=len(short), rows=list(indices),
                                 all_short=all_short, minor=determinant, gcd=common))
        work['hit_windows'] += int(len(hits) > before)
    factor = hits[0]['gcd'] if hits else None
    return dict(schedule=schedule, radius=radius, first_center=first, max_blocks=blocks,
                total_blocks=total, visited_blocks=visited, unvisited_blocks=total-visited,
                unvisited_prefix_blocks=prefix, unvisited_suffix_blocks=suffix,
                schedule_exhausted=(visited == total), work=dict(work), hits=hits, factor=factor,
                unsplit_n=None if factor else n, cpu_seconds=process_time()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', required=True, choices=('22663', '49', 'fresh-2048', 'crossed-2048'))
    parser.add_argument('--blocks', type=int)
    args = parser.parse_args()
    fixture = Path(__file__).resolve().parents[1] / 'benchmarks/quartic-three-row.json'
    case = next(row for row in json.loads(fixture.read_text())
                if row['id'] == 'quartic-three-row-' + args.case)
    cap = case['blocks'] if args.blocks is None else args.blocks
    if not 0 <= cap <= case['blocks']:
        parser.error('block cap is outside the published schedule')
    print(json.dumps(search(int(case['n']), schedule=case['schedule'], blocks=cap), indent=2))
