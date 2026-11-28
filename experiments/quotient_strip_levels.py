"""Compare short-interval factor searches using weighted integer levels and moments."""

import argparse
import json
import platform
from collections import Counter
from math import isqrt
from pathlib import Path
from statistics import median
from time import process_time_ns

from experiments.continued_square import convergents
from experiments.quotient_search import line_factors, sparse_root
from experiments.quotient_strip_localization import (
    MeasuredStrip, blocks, direct_trial, holdout_cohort, ratio_cohort,
)


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/quotient-strip-levels.json'
METHODS = ('chord', 'chord_parity', 'chord_mod8', 'triangle_parity', 'covariance_parity', 'recursive_line')


def schedule(n):
    """Balanced band and twice the nearest sixth root, via a logarithmic search."""
    if n < 1:
        raise ValueError('Expected a positive product')
    lo, hi = 0, 1 << ((n.bit_length()+5)//6)
    while lo < hi:
        mid = (lo+hi)//2
        if (2*mid+1)**6 < 64*n:
            lo = mid+1
        else:
            hi = mid
    return isqrt((n-1)//2)+1, isqrt(n), 2*lo


def chord_levels(n, a, b, triangle, work):
    """Return a direction and an inclusive range for u*x+v*y, using integer endpoints."""
    if n < 1 or not 1 <= a <= b:
        raise ValueError('Expected a positive product and 1 <= a <= b')
    d = b-a
    limit = max(1, d//2)
    for p, q in convergents(n, a*b):
        work['cf_divmods'] += 1
        if q > limit:
            break
        u, v = p, q
    if abs(u*a*b-v*n)*(limit+1) > a*b:
        raise ArithmeticError('Convergent failed its scaled-error bound')
    den = 4*a*a*b
    left = 4*a*b*(u*a*a+v*n)
    right = 4*a*a*(u*b*b+v*n)
    if triangle:
        third = 4*b*(u*b*a*a+v*n*(2*a-b))
        lo = min(left, right, third)
        hi = max(left, right, third)
    else:
        lo = min(left, right)-v*n*d*d
        hi = max(left, right)
    work['level_endpoint_divisions'] += 2
    return u, v, -((-lo)//den), hi//den


def shortest_direction(A, B, C, work):
    """Binary lattice reduction for a positive definite integral covariance form."""
    def dot(x, y):
        return A*x[0]*y[0]+B*(x[0]*y[1]+x[1]*y[0])+C*x[1]*y[1]

    p, q = (1, 0), (0, 1)
    while True:
        work['reduction_iterations'] += 1
        if dot(p, p) > dot(q, q):
            p, q = q, p
        v, cross = dot(p, p), dot(p, q)
        if 2*abs(cross) <= v:
            return p
        step = (2*cross+v)//(2*v)
        work['reduction_divisions'] += 1
        q = q[0]-step*p[0], q[1]-step*p[1]


def solve_levels(n, a, b, direction, parity, work, mod8=False):
    u, v, low, high = direction
    count = max(0, high-low+1)
    work['bounded_levels'] += count
    work[f'blocks_with_{count}_levels'] += 1
    step = 2 if parity and n % 2 else 1
    first = low+(u+v-low)%2 if step == 2 else low
    if first > high:
        return
    residues = None
    if mod8 and n % 2:
        label = (u+(n % 8)*v) % 8
        residues = {label*j % 8 for j in (1, 3, 5, 7)}
        work['mod8_residues_generated'] += 4
    for z in range(first, high+1, step):
        if residues is not None:
            work['mod8_membership_tests'] += 1
            if z % 8 not in residues:
                continue
        work['tested_levels'] += 1
        if u*v:
            disc = z*z-4*u*v*n
            if disc < 0:
                continue
            work['discriminant_square_roots'] += 1
            root = isqrt(disc)
            if root*root != disc:
                continue
            numerators = (z-root, z+root) if root else (z,)
            candidates = []
            for s in numerators:
                work['root_divmods'] += 1
                x, r = divmod(s, 2*u)
                if not r:
                    candidates.append(x)
        else:
            # A coordinate direction fixes x or y directly.
            divisor = u or v
            work['root_divmods'] += 1
            value, rem = divmod(z, divisor)
            if rem or value <= 0:
                continue
            if u:
                candidates = [value]
            else:
                work['coordinate_divmods'] += 1
                x, rem = divmod(n, value)
                candidates = [] if rem else [x]
        for x in candidates:
            if a <= x <= b:
                work['divisibility_tests'] += 1
                y, r = divmod(n, x)
                if not r and u*x+v*y == z:
                    yield x


def moment_search(n, a, b, method, work):
    box = MeasuredStrip(n, a, b)
    c = box.count()
    work['moment_strips'] += 1
    if not c:
        work.update(box.costs())
        return
    if method == 'covariance_parity' and c <= 3:
        status, x = sparse_root(box, c)
        if status != 'multiple':
            work.update(box.costs())
            if status == 'factor':
                work['divisibility_tests'] += 1
                if not a <= x <= b or n % x:
                    raise ArithmeticError('Invalid sparse reconstruction')
                yield x
            return
    if a == b:
        work.update(box.costs())
        work['divisibility_tests'] += 1
        if n % a == 0:
            yield a
        return
    hits = line_factors(box, c)
    if hits is not None:
        work.update(box.costs())
        yield from sorted(hits)
        return
    if method == 'recursive_line':
        work.update(box.costs())
        mid = (a+b)//2
        work['bisections'] += 1
        yield from moment_search(n, a, mid, method, work)
        yield from moment_search(n, mid+1, b, method, work)
        return
    sx, sy = box.moment(1, 0), box.moment(0, 1)
    xx, xy, yy = box.moment(2, 0), box.moment(1, 1), box.moment(0, 2)
    A, B, C = c*xx-sx*sx, c*xy-sx*sy, c*yy-sy*sy
    if A <= 0 or A*C <= B*B:
        raise ArithmeticError('Expected a rank-two cloud after line recovery')
    u, v = shortest_direction(A, B, C, work)
    total = u*sx+v*sy
    radius = isqrt((c-1)*(u*u*A+2*u*v*B+v*v*C))
    work.update(box.costs())
    work.update(covariance_square_roots=1, level_endpoint_divisions=2)
    yield from solve_levels(n, a, b, (u, v, -((radius-total)//c), (radius+total)//c), True, work)


def scan(n, method, stop=False):
    """Scan blocks from left to right; a first hit can stop within a level loop."""
    work, hits = Counter(), []
    first = None
    low, high, width = schedule(n)
    for a in range(low, high+1, width):
        b = min(a+width-1, high)
        work['initial_blocks'] += 1
        if method in ('covariance_parity', 'recursive_line'):
            answers = moment_search(n, a, b, method, work)
        elif a == b:
            work.update(singleton_columns=1, divisibility_tests=1)
            answers = [a] if n % a == 0 else []
        else:
            direction = chord_levels(n, a, b, method == 'triangle_parity', work)
            answers = solve_levels(n, a, b, direction, method != 'chord', work, mod8=method == 'chord_mod8')
        for x in answers:
            hits.append(x)
            if first is None:
                first = work.copy()
            if stop:
                return hits, work, first
    return hits, work, first


def compare(pairs):
    methods = {name: {'complete': Counter(), 'to_first': Counter()} for name in METHODS}
    trial = Counter()
    for p, q in pairs:
        n = p*q
        lo, hi, width = schedule(n)
        if [(a, min(a+width-1, hi)) for a in range(lo,hi+1,width)] != blocks(n):
            raise ArithmeticError('Public block schedule disagrees with comparison')
        for name in METHODS:
            hits, complete, first = scan(n, name)
            if hits != [p]:
                raise ArithmeticError(f'{name} returned {hits} at {n}')
            methods[name]['complete'].update(complete)
            methods[name]['to_first'].update(first)
        factor, first, full = direct_trial(n)
        if factor != p:
            raise ArithmeticError(f'Odd trial failed for {n}')
        trial.update(to_first=first, complete=full)
    return dict(products=len(pairs), methods=methods, direct_odd_divisions=trial)


def full_width():
    repo = FIXTURE.parents[1]
    controls = json.loads((repo/'benchmarks/endpoint-offset-product.json').read_text())
    n = int(next(r['n'] for r in controls if r['id'] == 'endpoint-offset-fresh-2048'))
    low, high, width = schedule(n)
    count = (high-low)//width+1

    def visit(index):
        a = low+index*width
        b = min(a+width-1, high)
        work = Counter()
        weights = chord_levels(n, a, b, False, work)
        u, v, left, right = weights
        hits = list(solve_levels(n, a, b, weights, True, work, mod8=True))
        return dict(index=str(index), endpoints=[str(a),str(b)],
                    slope=[str(u),str(v)], levels=[str(left),str(right)],
                    recovered=[str(x) for x in hits], work=work)

    public = [visit(i) for i in (0,count//3,2*count//3,count-1)]
    # The public indices are fixed before reading either certified prime.
    certificate = json.loads((repo/'research/certified-control.json').read_text())
    p, q = sorted(int(chain[-1]['prime']) for chain in certificate['chains'].values())
    if p*q != n:
        raise ArithmeticError('Fresh control and certified primes disagree')
    supplied = visit((p-low)//width)
    for row in [*public, supplied]:
        a, b = map(int, row['endpoints'])
        if (row['recovered'] != ([str(p)] if a <= p <= b else []) or
                row['work']['bounded_levels'] > 5):
            raise ArithmeticError('Full-width control disagrees with certificate or level bound')
    return dict(input_id='endpoint-offset-fresh-2048', product_bits=n.bit_length(),
                block_count=str(count), nominal_width=str(width), public_blocks=public,
                factor_selected_block=supplied)


def larger_controls():
    source = json.loads(FIXTURE.with_name('modular-hyperbola.json').read_text())
    selected = ('modular-hyperbola-41', 'modular-hyperbola-holdout-binary-46')
    results = []
    for input_id in selected:
        fixture = next(row for row in source if row['id'] == input_id)
        n = int(fixture['n'])
        hits, complete, first = scan(n, 'chord_mod8')
        p, to_first, all_odd = direct_trial(n)
        if hits != [p] or [str(p),str(n//p)] != fixture['factors']:
            raise ArithmeticError(f'Larger control {input_id} disagrees with the certificate')
        results.append(dict(input_id=input_id, source='benchmarks/modular-hyperbola.json',
                            product=str(n), recovered=[str(p),str(n//p)],
                            chord_mod8=dict(complete=complete, to_first=first),
                            direct_odd_divisions=dict(complete=all_odd, to_first=to_first)))
    return results


def simple_odd(n, stop):
    """Direct ascending odd trial for timing, collecting answers without per-row instrumentation."""
    hits = []
    for x in range((isqrt((n-1)//2)+1) | 1, isqrt(n)+1, 2):
        if n % x == 0:
            hits.append(x)
            if stop:
                break
    return hits


def time_group(pairs, names, repetitions):
    # Rotate the order; each timed search gets the product alone, with identical
    # whole-band or first-hit stopping semantics. Validate hits outside the clock.
    for stop in (False, True):
        rows = {name: [] for name in names}
        for repetition in range(repetitions):
            rotation = repetition % len(names)
            for name in names[rotation:]+names[:rotation]:
                start = process_time_ns()
                if name == 'direct_odd':
                    answers = [simple_odd(n, stop) for n, _ in pairs]
                else:
                    answers = [scan(n, name, stop)[0] for n, _ in pairs]
                rows[name].append(process_time_ns()-start)
                if answers != [[p] for _,p in pairs]:
                    raise ArithmeticError('Timing method returned incorrect factors')
        print('to_first' if stop else 'complete', 'median CPU ms',
              {name: round(median(values)/1e6,3) for name, values in rows.items()})


def study():
    # Also exercise the enclosure outside the balanced schedule, including u=0.
    trials = 0
    for n in range(1, 81):
        for a in range(1, 12):
            for b in range(a, a+7):
                expected = [x for x in range(a, b+1) if n % x == 0]
                for triangle in (False, True):
                    work = Counter()
                    direction = chord_levels(n, a, b, triangle, work)
                    got = sorted(solve_levels(n, a, b, direction, True, work, mod8=True))
                    if got != expected:
                        raise ArithmeticError(f'Geometric bounds failed for {n}, {a}, {b}')
                trials += 1
    n, a, b = 3574327, 1678, 1710
    work = Counter()
    u, v, low, high = chord_levels(n, a, b, False, work)
    control = dict(product=str(n), supplied_interval=[a,b], slope=[u,v], levels=[low,high],
                   hits=list(solve_levels(n, a, b, (u,v,low,high), True, work)), work=work)
    return dict(scope='Same 99 prescribed-ratio products and 64 holdout products and same ascending blocks as the quotient-strip localization receipt. The extra supplied strip is outside the cohort counts.',
                selection='At endpoints a,b, choose the last convergent u/v of N/(a*b) with v <= max(1,floor((b-a)/2)). The chord method subtracts v*N*(b-a)^2/(4*a^2*b) from the smaller weighted endpoint. The comparison triangle also evaluates the tangent at b. Parity uses z = u+v mod 2 on odd products. The mod-8 refinement keeps the residues (u+Nv)*j for the four odd j modulo eight.',
                costs='First-hit counters snapshot the successful level, or the completed sparse or collinear solver. Level-square-root counts exclude line equations, which are recorded separately. CF steps are Euclidean divmods. Shared block scheduling and reference checks are excluded. The covariance control uses the same sparse/line shortcuts as localization and the shortest integer projection thereafter. The recursive comparison bisects each noncollinear strip.',
                small_intervals=trials, supplied_control=control, fresh=full_width(),
                larger_control_selection="Previously published 41-bit modular-hyperbola example and its 46-bit holdout control. Selection is for a repeatable comparison. Both searches receive only the decimal product.",
                larger_controls=larger_controls(), ratio=compare(ratio_cohort()),
                holdout=compare(holdout_cohort()))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timings', action='store_true', help='also time the 12-product sample and two larger controls')
    args = parser.parse_args()
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Quotient-level costs differ from the reviewed fixture')
    print(f"Verified both geometric enclosures on {result['small_intervals']} intervals, six searches on 163 products and five full-width blocks.")
    if args.timings:
        print('Timing environment', platform.python_implementation(), platform.python_version(),
              platform.platform(), platform.machine())
        print('Geometry and moment methods include their operation counters. Direct odd trial uses a simple loop. Input preparation and result verification are excluded.')
        sample = [(p*q,p) for p,q in ratio_cohort()[::17]+holdout_cohort()[::11]]
        print('Small products:', len(sample), 'three rotated repetitions')
        time_group(sample, (*METHODS, 'direct_odd'), 3)
        for row in result['larger_controls']:
            print(row['input_id'], 'five alternating repetitions')
            time_group([(int(row['product']),int(row['recovered'][0]))], ('chord_mod8','direct_odd'), 5)
