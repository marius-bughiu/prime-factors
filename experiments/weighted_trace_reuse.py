"""Use both integer branches of one weighted trace strip in a divisor-interval sweep.

Hiary already extends the interval asymmetrically with the same convergent.
Here two exact quadratic inequalities give the full preimage, including a
possible second component. A priority queue revisits that component for free
once all earlier positions are checked. The preset compares full covers as
well as first-hit searches under the equal-factor-width assumption.
"""

import argparse
from heapq import heappop, heappush
import json
from math import isqrt
from pathlib import Path
from time import process_time_ns

from .affine_radix_holdout import draw_prime
from .continued_square import convergents
from .offset_tangent_cover import cube_root

ROOT = Path(__file__).resolve().parents[1]
MODES = ('fixed', 'connected', 'both', 'fixed24', 'connected24', 'both24', 'hiary')
FRONTIER = ('connected24','both24','best24')
SEED = b'two-branch-trace-cover-v1'
BITS = (19, 20, 21, 19, 20, 21, 19, 20)


def _slab(a, product, level, strict, cost):
    """Integer x with (2ax-level)^2 <= level²-4abN (strict when requested)."""
    delta = level*level-product-int(strict)
    if delta < 0:
        return None
    root = isqrt(delta)
    cost['boundary_roots'] += 1
    low = (level-root+2*a-1)//(2*a)
    high = (level+root)//(2*a)
    return (low, high) if low <= high else None


def components(n, a, b, z, low, high, cost, stride=2):
    """Inclusive positive integer intervals with z-stride < ax+bN/x < z+stride."""
    product = 4*a*b*n
    outer = _slab(a, product, z+stride, True, cost)
    if outer is None:
        return []
    left, right = max(low, outer[0]), min(high, outer[1])
    if right < left:
        return []
    hole = _slab(a, product, z-stride, False, cost)
    if hole is None:
        return [(left, right)]
    return [(l, h) for l, h in ((left,min(right,hole[0]-1)), (max(left,hole[1]+1),right))
            if l <= h]


def _possible(n, a, b, z, l, h):
    """Does the continuous image of this closed interval contain z?"""
    bn = b*n
    left = a*l*l - z*l + bn
    right = a*h*h - z*h + bn
    if max(left, right) < 0:
        return False
    if a*l*l >= bn:
        return left <= 0
    if a*h*h <= bn:
        return right <= 0
    return z > 0 and z*z >= 4*a*bn


def _contains(n, a, b, z, stride, x, y):
    """Sufficient continuous test for a strict extension of the current prefix."""
    bn = b*n
    upper = z+stride
    lx, ry = a*x*x+bn, a*y*y+bn
    if lx >= upper*x or ry >= upper*y:
        return False
    lower = z-stride
    if a*x*x >= bn:
        return lx > lower*x
    if a*y*y <= bn:
        return ry > lower*y
    return lower <= 0 or lower*lower < 4*a*bn


def _frontier(n, directions, a, b, z, windows, x, high, work):
    """Keep a direction only when its trace strip extends the current covered prefix."""
    for u,v in reversed(directions):
        if u <= 0 or windows[0][1] == high:
            continue
        residue = u+v*n
        floor_trace = residue+24*((u*x*x+v*n-residue*x)//(24*x))
        for t in (floor_trace, floor_trace+24):
            if (u,v,t) == (a,b,z) or windows[0][1] == high:
                continue
            work['direction_guards'] += 1
            if not _contains(n,u,v,t,24,x,windows[0][1]+1):
                continue
            new = components(n,u,v,t,x,high,work,24)
            if new[0][0] != x or new[0][1] <= windows[0][1]:
                raise ArithmeticError('guard failed to certify a longer connected prefix')
            a,b,z,windows = u,v,t,new
            work['direction_updates'] += 1
    return a,b,z,windows


def search(n, mode, *, max_setups=None, stop_at_factor=False):
    if n < 15 or n%2 == 0 or mode not in MODES+FRONTIER:
        raise ValueError('expected odd N >= 15 and a listed mode')
    if max_setups is not None and max_setups < 0:
        raise ValueError('negative setup budget')
    start = process_time_ns()
    half = (n.bit_length()+1)//2
    cap = (1<<half)-1
    low = max(1<<(half-1), (n+cap-1)//cap, isqrt((n-1)//2)+1)
    high = isqrt(n)
    strategy = mode.removesuffix('24')
    scale = 12 if mode.endswith('24') else 1
    if scale == 12 and n % 3 == 0:
        raise ValueError('mod-24 weights require N coprime to six')
    shift = n % 12 if scale == 12 else 0
    w = cube_root(scale*(low-1)//4)
    if 4*w**3 >= scale*(low-w):
        w -= 1
    if low > high or w < 1:
        raise ValueError('requires a nonempty eligible interval and a positive safe radius')
    hl = cube_root(low**3//(17*n)) if mode == 'hiary' else None
    if hl is not None and hl < 1:
        raise ValueError('Hiary loop requires center beyond the trial-division section')
    x = low
    pending = []
    divisors = set()
    work = dict(setups=0, euclidean_divisions=0, boundary_roots=0, interval_tests=0,
                discriminant_roots=0, root_candidates=0, divisor_tests=0, secondary_insertions=0,
                queue_pops=0, queue_positions=0, peak_queue=0, radius_comparisons=0,
                setup_cube_roots=1+int(hl is not None), direction_guards=0, direction_updates=0)
    while x <= high and (max_setups is None or work['setups'] < max_setups):
        work['setups'] += 1
        if strategy == 'hiary':
            # Hiary §4 with its 0.4/0.6 bounds; choose the left half at
            # x, which remains safe at the slightly larger center c.
            while True:
                work['radius_comparisons'] += 1
                if 17*n*(hl+1)**3 > x**3:
                    break
                hl += 1
            c = min(x+hl,high)
            limit = 4*hl
        else:
            c = min(x+w,high)
            limit = 2*w
        csq = c*c
        directions = [] if strategy == 'best' else None
        for p,q in convergents(n+shift*csq, scale*csq):
            work['euclidean_divisions'] += 1
            if q > limit:
                break
            a,b = scale*p-shift*q,q
            if directions is not None:
                directions.append((a,b))
        if strategy == 'hiary':
            nearest = (2*b*n+c-1)//(2*c)
            remaining = c-abs(b*n-nearest*c)
            slope_error = abs(a*csq-b*n)
            right = isqrt(3*remaining*csq//(5*b*n))
            work['boundary_roots'] += 1
            if slope_error:
                right = min(right,2*remaining*c//(5*slope_error))
            z = nearest+a*c
            windows = [(x,min(c+right,high))]
        else:
            if abs(a*csq-b*n)*(2*w+1) > scale*csq or b*n*w*w > scale*csq*(c-w):
                raise ArithmeticError('chosen weights failed the one-trace hypotheses')
            parity = a+b if scale == 1 else a+b*n
            stride = 2*scale
            z = parity+stride*((2*(a*csq+b*n)+3*scale*c-1-2*c*parity)//(2*stride*c))
            end = min(c+w,high)
            windows = [(x,end)]
            if strategy != 'fixed':
                windows = components(n,a,b,z,x,high,work,stride)
                if not windows or windows[0][0] != x or windows[0][1] < end:
                    raise ArithmeticError('strip did not contain the guaranteed window')
                if strategy == 'connected':
                    windows = windows[:1]
        if directions is not None:
            a,b,z,windows = _frontier(n,directions,a,b,z,windows,x,high,work)
        for l,h in windows:
            work['interval_tests'] += 1
            if (z-a-b)%2 == 0 and _possible(n,a,b,z,l,h):
                delta = z*z-4*a*b*n
                root = isqrt(delta)
                work['discriminant_roots'] += 1
                if root*root == delta:
                    for numerator in sorted({z-root,z+root}):
                        item, remainder = divmod(numerator,2*a)
                        work['root_candidates'] += 1
                        if remainder == 0 and low <= item <= high:
                            work['divisor_tests'] += 1
                            if n%item == 0:
                                divisors.add(item)
                break
        x = windows[0][1]+1
        if len(windows) == 2:
            heappush(pending, windows[1])
            work['secondary_insertions'] += 1
            work['peak_queue'] = max(work['peak_queue'], len(pending))
        while pending and pending[0][0] <= x:
            _,end = heappop(pending)
            work['queue_pops'] += 1
            work['queue_positions'] += max(0,end+1-x)
            x = max(x,end+1)
        if stop_at_factor and divisors:
            break
    return dict(divisors=sorted(divisors), lower=low, upper=high, fixed_radius=None if mode == 'hiary' else w,
                prefix_covered=x-low, remaining_prefix_to_upper=high+1-x, full_cover=x>high,
                work=work, cpu_ns=process_time_ns()-start)


def panel(*, verify=False, frontier=False):
    from scripts.factor import render_certificate, verify_file
    seed = b'two-branch-weight-frontier-v1' if frontier else SEED
    modes = FRONTIER if frontier else MODES
    cases = []
    seen = set()
    attempt = 0
    for i,bits in enumerate(BITS):
        while True:
            pair = sorted(draw_prime(side,attempt,bits=bits,seed=seed) for side in (b'p',b'q'))
            attempt += 1
            n = pair[0]*pair[1]
            if pair[0] != pair[1] and n.bit_length()==2*bits and n not in seen:
                seen.add(n)
                break
        runs = {}
        order = modes[i%len(modes):]+modes[:i%len(modes)]
        for stop in (False,True):
            for mode in order:
                trial = search(n,mode,stop_at_factor=stop)
                if trial['divisors'] != pair[:1] or (not stop and not trial['full_cover']):
                    raise RuntimeError('search did not recover the expected smaller prime')
                runs[mode+('_first' if stop else '_full')] = trial
        if verify:
            path = ROOT/'build'/'weighted-trace-reuse'/f'{n}.lean'
            path.parent.mkdir(parents=True,exist_ok=True)
            divisor = runs[modes[-1]+'_full']['divisors'][0]
            path.write_text(render_certificate(n,[divisor,n//divisor]))
            verify_file(path)
        cases.append(dict(n=str(n),attempt=attempt-1,factors=list(map(str,pair)),runs=runs))
    controls = []
    for c in json.loads((ROOT/'research'/'reciprocal-sum-lanes.json').read_text())['control_sections']:
        if c['end']=='first':
            controls.append(dict(input=c['input'],n=c['n'],max_setups=8,
                                 runs={mode:search(int(c['n']),mode,max_setups=8) for mode in modes}))
    return dict(seed=seed.decode(),cases=cases,controls=controls)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify',action='store_true')
    parser.add_argument('--frontier',action='store_true')
    args = parser.parse_args()
    print(json.dumps(panel(verify=args.verify,frontier=args.frontier),indent=2))
