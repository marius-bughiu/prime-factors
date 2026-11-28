"""Measure sparse valuation progressions on the bounded hard-target cohort."""

from collections import Counter
from functools import lru_cache
from heapq import merge
from itertools import combinations
import json
from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.circle_mark_prefix_skip import band_search, choose_target
from experiments.circle_mark_reduced import reduced_search
from scripts.factor import primes_through, render_certificate, verify_file

FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/circle-mark-dyadic-lanes.json'
DEPTHS = (3, 5, 8)


@lru_cache(maxsize=None)
def progressions(target, depth):
    """Return (residue, stride, known multiplier) lanes; zero means unresolved."""
    if target % 8 != 1 or depth < 3:
        raise ValueError('expected a one-mod-eight target and depth at least three')
    persistent = (1, 3)
    resolved = [(0, 2, 1)]
    for j in range(3, depth + 1):
        stride = 1 << j
        children = [r + offset for r in persistent for offset in (0, stride // 2)]
        persistent = []
        for r in children:
            excess = (r * r - target) % (2 * stride)
            if excess == 0:
                persistent.append(r)
            elif excess == stride:
                resolved.append((r, stride, stride))
            else:
                raise ArithmeticError('child failed its parent congruence')
        if len(persistent) != 2:
            raise ArithmeticError('wrong number of lifting classes')
    return tuple(resolved + [(r, stride, 0) for r in persistent])


def coordinates(lane, target, lower, upper, cutoff, finish, work):
    residue, stride, scale = lane
    if not scale:
        # The unspecialized lanes still have at least this known two-part.
        start = 1 + isqrt(target + 2 * stride * lower - 1)
        work['square_roots'] += 1
        start += (residue - start) % stride
        for x in range(start, finish + 1, stride):
            difference = x * x - target
            odd_part = difference // (difference & -difference)
            work['deep_classifications'] += 1
            if odd_part <= (odd_part // lower) * upper:
                work['yielded'] += 1
                yield x
        return

    for k in range(1, cutoff + 1):
        start = 1 + isqrt(target + scale * k * lower - 1)
        work['square_roots'] += 1
        start += (residue - start) % stride
        if start > finish:
            return
        end = finish
        if k < cutoff:
            end = min(finish, isqrt(target + scale * k * upper))
            work['square_roots'] += 1
        for x in range(start, end + 1, stride):
            work['yielded'] += 1
            yield x
        if end == finish:
            return


def search(n, target, width, depth):
    lower = (n >> width) + 1
    upper = (1 << width) - 1
    cutoff = 1 + (lower - 2) // (upper - lower)
    work = dict(gcds=0, square_roots=0, deep_classifications=0, yielded=0)
    streams = [coordinates(lane, target, lower, upper, cutoff, upper // 2, work)
               for lane in progressions(target, depth)]
    for x in merge(*streams):
        work['gcds'] += 1
        d = gcd(n, x * x - target)
        if d > 1:
            work['unused_lookahead'] = work.pop('yielded') - work['gcds']
            return x, d, work
    raise ArithmeticError('no mark within the factor-width bound')


def study():
    targets = Counter()
    totals = {depth: Counter() for depth in DEPTHS}
    controls = Counter()
    example = None
    for width in range(7, 13):
        upper = 1 << width
        primes = [p for p in primes_through(upper - 1) if p >= upper // 2]
        for p, q in combinations(primes, 2):
            n = p * q
            if n.bit_length() != 2 * width:
                continue
            target, early = choose_target(n)
            if early is not None or target % 8 != 1:
                continue
            targets[target] += 1
            reference = reduced_search(n, target, width, record_controls=False)
            raw = band_search(n, target, width)
            expected = raw['first_x'], raw['divisor']
            if expected != (reference['first_x'], reference['divisor']) or expected[1] not in (p, q):
                raise ArithmeticError('reference searches disagree with each other or prime labels')
            controls.update(dict(raw_gcds=raw['band_gcds'], raw_square_roots=raw['square_roots'],
                                 full_classifications=(reference['first_x'] - reference['prefix']), full_gcds=reference['gcds']))
            runs = {}
            for depth in DEPTHS:
                x, d, work = search(n, target, width, depth)
                if (x, d) != expected or work['gcds'] != reference['gcds']:
                    raise ArithmeticError('sparse search changed the first mark or gcd count')
                totals[depth].update(work)
                runs[str(depth)] = work
            # A fixed small example selected in increasing factor-width and prime-pair order.
            if example is None:
                example = dict(product=str(n), factors=[str(f) for f in sorted((d, n // d))], target=target,
                               first_x=x, found_divisor=str(d), work=runs,
                               raw_gcds=raw['band_gcds'], full_classifications=(reference['first_x'] - reference['prefix']))
    tables = {str(a): {str(k): dict(lanes=len(progressions(a, k)),
                                    unresolved=sorted(r for r, _, c in progressions(a, k) if not c),
                                    child_residue_tests=4 * (k - 2)) for k in DEPTHS} for a in targets}
    return dict(targets={str(a): count for a, count in sorted(targets.items())},
                setup_per_distinct_target_and_depth=tables, reference=dict(controls),
                by_depth={str(k): dict(totals[k]) for k in DEPTHS}, example=example)


def main():
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('sparse lane census differs from its reviewed fixture')
    example = result['example']
    n = int(example['product'])
    with TemporaryDirectory() as tmp:
        path = Path(tmp) / 'DyadicLanes.lean'
        path.write_text(render_certificate(n, [int(f) for f in example['factors']]))
        verify_file(path)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
