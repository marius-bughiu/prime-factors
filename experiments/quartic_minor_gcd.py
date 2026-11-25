"""Check the five normalized quartic minors on bounded windows of the published controls."""

import argparse
from collections import Counter
from itertools import combinations
import json
from math import gcd
from pathlib import Path
from time import process_time

from .quartic_basis_translation import reduce_window, window_layout


def direct_coordinates(rows, n):
    """Recompute the signed nonconstant minors divided by N, up to common basis sign."""
    coordinates = []
    for omitted in range(5):
        a,b,c,d = [row[1:] for i,row in enumerate(rows) if i != omitted]
        # Laplace expansion in the first two rows.
        determinant = 0
        for i,j in combinations(range(4),2):
            k,l = [z for z in range(4) if z != i and z != j]
            term = (a[i]*b[j]-a[j]*b[i])*(c[k]*d[l]-c[l]*d[k])
            determinant += term if (i+j)%2 else -term
        if omitted%2:
            determinant = -determinant
        coefficient, remainder = divmod(determinant,n)
        if remainder:
            raise ArithmeticError('nonconstant minor is not a multiple of N')
        coordinates.append(coefficient)
    return coordinates


def search(n, *, full, blocks, verify_minors=False):
    """Test gcds without a polynomial root search. A missed gcd does not exclude a divisor.

    Every basis represents N² = sum v_i P_i. Cramer's rule gives |v_i| equal
    to its omitted-row minor divided by N. Track the exact v_i through LLL.
    At an offset for a divisor p the row evaluations have gcd p². If just one
    row evaluates nonzero, it equals ±p², so its |v_i| is exactly (N/p)².
    Independent direct verification is optional and its work is counted separately.
    """
    if blocks is None or blocks < 0:
        raise ValueError('an explicit nonnegative block cap is required')
    start = process_time()
    layout = window_layout(n,full=full,blocks=blocks)
    w = layout['radius']
    scale = [w**i for i in range(5)]
    dual = [1,0,0,0,0]
    previous = None
    hits = []
    work = Counter({key:0 for key in (
        'lll_calls','lll_reductions','lll_swaps','translations','normalized_minor_gcds',
        'unit_gcds','whole_modulus_gcds','proper_gcds','hit_windows','integer_root_nodes',
        'direct_minors_verified','direct_proper_gcds')})
    for block in range(layout['visited_blocks']):
        center = layout['first_center']+2*block*(2*w+1)
        previous, _, short = reduce_window(n,center,w,scale,previous,work,dual_coordinates=dual)
        if verify_minors:
            direct = direct_coordinates(previous,n)
            if direct != dual and direct != [-v for v in dual]:
                raise ArithmeticError('direct minors disagree with the tracked coordinates')
            work['direct_minors_verified'] += len(direct)
            work['direct_proper_gcds'] += sum(1 < gcd(v,n) < n for v in direct)
        hits_before = len(hits)
        for row, coordinate in enumerate(dual):
            common = gcd(n,coordinate)
            work['normalized_minor_gcds'] += 1
            if common == 1:
                work['unit_gcds'] += 1
            elif common == n:
                work['whole_modulus_gcds'] += 1
            else:
                work['proper_gcds'] += 1
                hits.append(dict(block=block,center=center,omitted_row=row,rank=len(short),
                                 normalized_minor_abs=abs(coordinate),gcd=common))
        work['hit_windows'] += int(len(hits) > hits_before)
    factor = hits[0]['gcd'] if hits else None
    return dict(**layout,work=dict(work),verify_minors=verify_minors,hits=hits,factor=factor,
                unsplit_n=None if factor else n,schedule_exhausted=layout['unvisited_blocks']==0,
                cpu_seconds=process_time()-start)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',required=True,choices=('49','fresh-2048','crossed-2048'))
    parser.add_argument('--blocks',type=int,help='use fewer than the published number of windows')
    parser.add_argument('--verify-minors',action='store_true')
    args = parser.parse_args()
    fixture = Path(__file__).resolve().parents[1]/'benchmarks/quartic-minor-gcd.json'
    case = next(row for row in json.loads(fixture.read_text())
                if row['id'] == f'quartic-minor-gcd-{args.case}')
    blocks = case['blocks'] if args.blocks is None else args.blocks
    if not 0 <= blocks <= case['blocks']:
        parser.error('block cap is outside the published schedule')
    print(json.dumps(search(int(case['n']),full=case['full'],blocks=blocks,
                            verify_minors=args.verify_minors),indent=2))
