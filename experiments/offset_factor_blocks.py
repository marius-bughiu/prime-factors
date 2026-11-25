"""Select sharp signed-gap coordinates for bounded blocks of possible smaller factors."""

import argparse
import json
from math import isqrt

from experiments.offset_coordinate_gaps import chart
from experiments.offset_tangent_cover import shifted_bounds
from experiments.offset_winner_window import bounds


def parameters(n, shifted):
    if n < 5 or n % 2 == 0 or isqrt(n)**2 == n:
        raise ValueError('expected an odd nonsquare product at least five')
    return shifted_bounds(n) if shifted else bounds(n)


def endpoint_basis(t, h, endpoint):
    """Gauss reduce the integral Gram matrix of (c*s-T*v)^2+H*v^2."""
    left, right = (1, 0), (0, 1)
    a, b, c = endpoint**2, -endpoint*t, t*t+h
    iterations = 0
    while True:
        iterations += 1
        if a > c:
            left, right = right, left
            a, c = c, a
        if 2*abs(b) <= a:
            break
        nearest = (2*b+a)//(2*a)
        right = right[0]-nearest*left[0], right[1]-nearest*left[1]
        c += nearest*(nearest*a-2*b)
        b -= nearest*a

    # The Lean basis certificate uses determinant +1.
    if left[0]*right[1]-left[1]*right[0] == -1:
        right = -right[0], -right[1]
        b = -b
    return left, right, b, iterations


def quadratic_interval(a, center, constant):
    """Integer solutions to a*d²−center*d+constant ≤ 0 for a positive a."""
    disc = center*center-4*a*constant
    if disc < 0:
        return None
    radius = isqrt(disc)
    first = -((radius-center)//(2*a))
    last = (center+radius)//(2*a)
    return (first, last) if first <= last else None


def trial_interval(n, t, height, s, v, lower, upper):
    """Integer d in the block with d*s²+N*v²/d−2*T*s*v ≤ height."""
    interval = quadratic_interval(s*s, 2*t*s*v+height, n*v*v)
    if interval is None:
        return None
    first = max(lower, interval[0])
    last = min(upper, interval[1])
    return (first, last) if first <= last else None


def determinant_span(n, t, h, height, s, v):
    """All integers d satisfying height*R_d(s,v) < d*h, for a positive height and s."""
    if h <= 0 or height <= 0 or s <= 0 or v <= 0 or n != t*t+h:
        raise ValueError('expected positive heights and coordinates with N=T²+H')
    return quadratic_interval(height*s*s, 2*height*t*s*v+h, height*n*v*v+1)


def _select(n, box, lower, upper, parity):
    h, t, height = box['h'], box['T'], box['J']
    left, right, dot, steps = endpoint_basis(t, h, upper)
    diagonal_sign = 1 if dot <= 0 else -1
    diagonal = left[0]+diagonal_sign*right[0], left[1]+diagonal_sign*right[1]
    candidates = []
    oriented = []
    for s, v in (left, right, diagonal):
        if v < 0:
            s, v = -s, -v
        if not 1 <= v <= s <= 2*v:
            continue
        oriented.append((s,v))
        bound = height-(height-s-v) % 2 if parity else height
        interval = trial_interval(n, t, bound, s, v, lower, upper)
        if interval is not None:
            candidates.append(dict(s=s, v=v, lower=interval[0], upper=interval[1]))
    return dict(lower=lower, upper=upper, gauss_iterations=steps, directions=3,
                endpoint_directions=sorted(oriented), interval_tests=len(oriented),
                charts=sorted(candidates, key=lambda row:(row['v'],row['s'])))


def select_block(n, lower, upper, *, shifted=True, parity=True):
    """Candidate charts and inclusive trial intervals, before testing integer squares.

    The assumed smaller factor lies in [lower,upper] and has a positive primitive
    sharp representation with v ≤ s ≤ 2v. Parity uses odd factor labels to cap j.
    The reported trial intervals include all integers satisfying the rounded
    height inequality, including composite and even trials.
    """
    box = parameters(n, shifted)
    if lower < 1 or upper < lower or upper > isqrt(n) or 16*(upper-lower)**2 > box['h']:
        raise ValueError('expected a positive smaller-factor block with 16*(upper-lower)^2 <= H')
    return _select(n, box, lower, upper, parity)


def _extend(n, box, selected, lower, upper, size, block, stop, work):
    """Find a guide whose certified interval spans this and subsequent whole blocks."""
    lo = lower+block*size
    end = block+1
    guide = None
    for s,v in sorted({(1,1),*selected['endpoint_directions']}):
        work['guide_tests'] += 1
        h, t, height = box['h'], box['T'], box['J']
        if height*((lo*s-t*v)**2+h*v*v) >= lo*h:
            continue
        # Passing the strict test at lo guarantees a nonnegative discriminant
        # and at least one integral solution in this quadratic sublevel set.
        work['guide_interval_roots'] += 1
        _, right = determinant_span(n,t,h,height,s,v)
        last = stop if right >= upper else min(stop,(right-lower+1)//size)
        if last > end:
            end, guide = last, (s,v)
    return end, guide


def search(n, *, max_blocks, start_block=0, shifted=True, parity=True, max_tests=0,
           coalesce=False, max_reductions=None, from_end=False):
    """Cover consecutive canonical blocks and optionally check their distinct charts.

    The factor range assumes equal bit widths. Chart scans use the full offset
    window for each selected pair; reported factors must fall inside the visited
    blocks. max_blocks always counts covered canonical blocks. When coalescing,
    max_reductions can separately cap the number of endpoint bases constructed.
    from_end starts at the first block of a suffix of at most max_blocks.
    """
    if min(max_blocks, start_block, max_tests) < 0:
        raise ValueError('block and position budgets must be nonnegative')
    if max_reductions is not None and (not coalesce or max_reductions < 0):
        raise ValueError('a nonnegative reduction budget requires coalescing')
    if from_end and start_block:
        raise ValueError('from_end and a nonzero start_block cannot be combined')
    box = parameters(n, shifted)
    lower, upper = box['L'], isqrt(n)
    size = isqrt(box['h'])//4+1
    total = max(0, (upper-lower)//size+1)
    if from_end:
        start_block = max(0, total-max_blocks)
    if start_block > total:
        raise ValueError('starting block lies beyond the factor range')
    stop = min(total, start_block+max_blocks)
    charts = set()
    iterations = interval_tests = chart_intervals = empty_blocks = 0
    reductions = 0
    group_work = dict(guide_tests=0, guide_interval_roots=0, guide_regions=0)
    block = start_block
    while block < stop and (max_reductions is None or reductions < max_reductions):
        lo = lower+block*size
        selected = _select(n, box, lo, min(upper,lo+size-1), parity)
        reductions += 1
        iterations += selected['gauss_iterations']
        interval_tests += selected['interval_tests']
        end, guide = block+1, None
        if coalesce and end < stop:
            end, guide = _extend(n,box,selected,lower,upper,size,block,stop,group_work)
        if guide is None:
            chart_intervals += len(selected['charts'])
            empty_blocks += not selected['charts']
            charts.update((row['s'],row['v']) for row in selected['charts'])
        else:
            group_work['guide_regions'] += 1
            interval_tests += 1
            s,v = guide
            jmax = box['J']-((box['J']-s-v)%2 if parity else 0)
            span = trial_interval(n,box['T'],jmax,s,v,lo,min(upper,lower+end*size-1))
            occupied = 0
            if span is not None:
                charts.add(guide)
                occupied = (span[1]-lower)//size-(span[0]-lower)//size+1
            chart_intervals += occupied
            empty_blocks += end-block-occupied
        block = end
    visited = block-start_block
    visited_lower = lower+size*start_block
    visited_upper = min(upper,lower+size*block-1)
    scanned = positions = untested = bound_roots = 0
    candidate_lower = candidate_upper = 0
    hits = []
    for s,v in sorted(charts, key=lambda pair:(pair[1],pair[0])):
        if positions >= max_tests:
            break
        scan = chart(n,box,s,v,16,max_tests=max_tests-positions,lift_cap=8,trace_units=True)
        scanned += 1
        positions += scan['tested_positions']
        untested += scan['untested_intervals']
        bound_roots += scan['bound_roots']
        candidate_lower += scan['candidate_lower']
        candidate_upper += scan['candidate_upper']
        hits.extend(hit for hit in scan['hits'] if visited_lower <= int(hit[2]) <= visited_upper)
    result = dict(lower=lower, upper=upper, block_size=size, total_blocks=total, visited_blocks=visited,
                unvisited_blocks=total-visited, start_block=start_block, max_blocks=max_blocks,
                max_tests=max_tests, shifted=shifted, parity=parity, gauss_iterations=iterations,
                directions=3*reductions, interval_tests=interval_tests, chart_intervals=chart_intervals,
                empty_blocks=empty_blocks, unique_charts=len(charts), scanned_charts=scanned,
                unscanned_charts=len(charts)-scanned, tested_positions=positions,
                bound_roots=bound_roots, untested_intervals=untested, hits=sorted(hits),
                schedule_exhausted=(visited==total and scanned==len(charts) and untested==0))
    if coalesce:
        result.update(group_work,coalesce=True,max_reductions=max_reductions,endpoint_reductions=reductions,
                      coalesced_blocks=visited-reductions,unvisited_prefix_blocks=start_block,
                      unvisited_suffix_blocks=total-block,candidate_lower=candidate_lower,
                      candidate_upper=candidate_upper,
                      untested_chart_positions_lower=max(0,candidate_lower-positions) if untested else 0,
                      untested_chart_positions_upper=candidate_upper-positions if untested else 0)
    if from_end:
        result['from_end'] = True
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--block', nargs=2, type=int, metavar=('LOWER','UPPER'),
                        help='select charts for one supplied inclusive block')
    parser.add_argument('--start-block', type=int, default=0)
    parser.add_argument('--from-end', action='store_true', help='start at the first block of the requested suffix')
    parser.add_argument('--max-blocks', type=int, default=1)
    parser.add_argument('--max-tests', type=int, default=0)
    parser.add_argument('--coalesce', action='store_true',
                        help='cover consecutive blocks with a determinant certificate for one chart')
    parser.add_argument('--max-reductions', type=int, help='limit endpoint reductions in coalesced searches')
    parser.add_argument('--ordinary', action='store_true', help='use floor(sqrt(N)) as the base')
    parser.add_argument('--all-parities', action='store_true', help='omit the odd-factor parity refinement')
    args = parser.parse_args()
    options = dict(shifted=not args.ordinary, parity=not args.all_parities)
    if args.block:
        result = select_block(args.n,*args.block,**options)
    else:
        result = search(args.n,max_blocks=args.max_blocks,start_block=args.start_block,
                        max_tests=args.max_tests,coalesce=args.coalesce,
                        max_reductions=args.max_reductions,from_end=args.from_end,**options)
    print(json.dumps(result,indent=2))
