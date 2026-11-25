"""Compare fresh and translated exact LLL bases on public adjacent divisor windows."""

import argparse
from collections import Counter
import json
from math import isqrt
from pathlib import Path
from statistics import median
from time import process_time

from .norm_auxiliary import integer_roots, reduced_basis
from .quartic_divisor_window import checked_height, jet_basis, odd_quartile_center


def translate(row, h):
    """Ascending coefficients of P(x+h)."""
    a,b,c,d,e = row
    return [(((e*h+d)*h+c)*h+b)*h+a, ((4*e*h+3*d)*h+2*c)*h+b,
            (6*e*h+3*d)*h+c, 4*e*h+d, e]


def radius(n, lower):
    """Maximum W satisfying the published degree-four box count at this lower bound."""
    lo, hi = 0, lower
    threshold = lower**10
    multiplier = n**3 * 5**5
    while lo+1 < hi:
        mid = (lo+hi)//2
        if multiplier*mid**10 < threshold:
            lo = mid
        else:
            hi = mid
    if not lo:
        raise ValueError('no positive guaranteed radius')
    return lo


def reduce_window(n, center, w, scale, previous, work, *, dual_coordinates=None):
    """Reduce one public window and check both jet conditions before reporting short rows.

    A translated basis preserves the coordinates of the constant polynomial N².
    A fresh jet basis instead represents that polynomial by its first row.
    """
    t = -center*pow(2,-1,n) % n
    if 2*t > n:
        t -= n
    if previous is None:
        basis = jet_basis(n,t)
        if dual_coordinates is not None:
            dual_coordinates[:] = [1,0,0,0,0]
    else:
        basis = [translate(row,2*w+1) for row in previous]
        work['translations'] += 1
    scaled = [[entry*s for entry,s in zip(row,scale)] for row in basis]
    _, rows = reduced_basis(scaled,work,initial_coefficients=basis,dual_coordinates=dual_coordinates)
    heights = [checked_height(n,t,w,row) for row in rows]
    short = [i for i,height in enumerate(heights) if height < (center-2*w)**2]
    work[f'rank_{len(short)}'] += 1
    return rows, heights, short


def sweep(n, first_center, w, blocks, upper, warm, *, lower=1):
    if (n < 3 or n%2 == 0 or first_center%2 == 0 or first_center <= 2*w or
            w < 1 or blocks < 0 or not 1 <= lower <= upper):
        raise ValueError('expected a positive odd progression, valid search bounds and a nonnegative budget')
    work = Counter()
    factors = set()
    first_cpu = later_cpu = 0.0
    first_swaps = max_later_swaps = unresolved_odd = 0
    previous = None
    scale = [w**i for i in range(5)]
    begin = process_time()
    for block in range(blocks):
        start = process_time()
        c = first_center + 2*block*(2*w+1)
        before = work['lll_swaps']
        previous, heights, short = reduce_window(n,c,w,scale,previous if warm else None,work)
        even_rejected = any(previous[i][0]%2 for i in short)
        odd_rejected = any(sum(previous[i])%2 for i in short)
        if even_rejected and odd_rejected:
            work['joint_mod2_exclusions'] += 1
        elif short:
            selected = min(short,key=heights.__getitem__)
            for x in integer_roots(previous[selected],-w,w,work):
                work['divisor_tests'] += 1
                d = c+2*x
                if lower <= d <= upper and n%d == 0:
                    factors.add(d)
        else:
            work['unresolved_blocks'] += 1
            first_odd = max(lower|1,c-2*w)
            last_odd = min(upper-(upper%2 == 0),c+2*w)
            unresolved_odd += max(0,(last_odd-first_odd)//2+1)
        swaps = work['lll_swaps']-before
        if block == 0:
            first_swaps, first_cpu = swaps, process_time()-start
        else:
            max_later_swaps = max(max_later_swaps,swaps)
            later_cpu += process_time()-start
    elapsed = process_time()-begin
    return dict(blocks=blocks,radius=w,work=dict(work),divisors=sorted(factors),cpu_seconds=elapsed,
                first_cpu=first_cpu,later_cpu=later_cpu,first_swaps=first_swaps,
                later_swaps=work['lll_swaps']-first_swaps,max_later_swaps=max_later_swaps,
                unresolved_odd_integers=unresolved_odd)


def window_layout(n, *, full, blocks=None):
    """Compute the equal-width window budget from N or start at its odd lower quartile.

    A block holds 2W+1 consecutive odd candidates. An optional block cap applies
    from the chosen start. The quartile schedule uses five blocks by default.
    """
    if n < 3 or n%2 == 0 or (blocks is not None and blocks < 0):
        raise ValueError('expected an odd input at least three and a nonnegative optional block cap')
    bits = (n.bit_length()+1)//2
    cap = (1<<bits)-1
    lower = max(1<<(bits-1),(n+cap-1)//cap)
    upper = isqrt(n)
    first_odd, last_odd = lower|1, upper-(upper%2 == 0)
    if first_odd > last_odd:
        raise ValueError('the equal-width range has no odd candidate')
    if full:
        w = radius(n,first_odd)
        first = first_odd+2*w
    else:
        if n.bit_length() != 2048:
            raise ValueError('the fixed-radius quartile schedule requires a 2048-bit input')
        w = 1<<407
        first = odd_quartile_center(n)
    size = 2*w+1
    first_lower = first-2*w
    prefix_odd = max(0,(min(last_odd+2,first_lower)-first_odd)//2)
    available = max(0,(last_odd-first_lower)//(2*size)+1)
    max_blocks = (available if full else 5) if blocks is None else blocks
    visited = min(max_blocks,available)
    odd_count = (last_odd-first_odd)//2+1
    last_visited = min(last_odd,first_lower+2*size*visited-2)
    visited_odd = max(0,(last_visited-max(first_odd,first_lower))//2+1)
    prefix_blocks = (prefix_odd+size-1)//size
    suffix_blocks = available-visited
    return dict(radius=w,full=full,range_lower=lower,range_upper=upper,first_odd=first_odd,
                last_odd=last_odd,even_integers=upper-lower+1-odd_count,first_center=first,
                total_blocks=prefix_blocks+available,available_blocks=available,max_blocks=max_blocks,
                visited_blocks=visited,unvisited_prefix_blocks=prefix_blocks,
                unvisited_suffix_blocks=suffix_blocks,unvisited_blocks=prefix_blocks+suffix_blocks,
                visited_odd_integers=visited_odd,unvisited_odd_integers=odd_count-visited_odd)


def search(n, *, full, blocks=None):
    """Run translated quartic root searches under the chosen window budget."""
    layout = window_layout(n,full=full,blocks=blocks)
    result = sweep(n,layout['first_center'],layout['radius'],layout['visited_blocks'],
                   layout['range_upper'],True,lower=layout['range_lower'])
    exhausted = not layout['unvisited_odd_integers'] and not result['unresolved_odd_integers']
    return {**layout, **result, 'exhausted':exhausted}


def compare(n, first, w, count, end, rounds):
    runs = {'fresh':[], 'translated':[]}
    for repeat in range(rounds):
        for mode in (('fresh','translated') if repeat%2 == 0 else ('translated','fresh')):
            runs[mode].append(sweep(n,first,w,count,end,mode=='translated'))
    result = {}
    for name,values in runs.items():
        out = values[0].copy()
        for key in ('cpu_seconds','first_cpu','later_cpu'):
            out[key] = median(r[key] for r in values)
        result[name] = out
    if result['fresh']['divisors'] != result['translated']['divisors']:
        raise AssertionError('the two searches returned different divisors')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',choices=['small','controls'],required=True)
    parser.add_argument('--rounds',type=int,default=1)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('rounds must be positive')
    if args.case == 'small':
        n = 502005281288939
        bits = (n.bit_length()+1)//2
        start = max(1<<(bits-1), (n+(1<<bits)-2)//((1<<bits)-1)) | 1
        end = isqrt(n)
        w = radius(n,start)
        count = (end-start)//(2*(2*w+1))+1
        print(json.dumps(compare(n,start+2*w,w,count,end,args.rounds),indent=2))
    else:
        fixture = Path(__file__).resolve().parents[1]/'benchmarks/quartic-divisor-window.json'
        for row in json.loads(fixture.read_text()):
            n = int(row['n'])
            if n.bit_length() == 2048:
                w = 1<<407
                print(row['id'],json.dumps(compare(n,odd_quartile_center(n),w,5,isqrt(n),args.rounds),indent=2))
