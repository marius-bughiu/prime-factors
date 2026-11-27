"""Compare every square and both half-trace gcds before and after contracting dilations."""
from math import gcd, isqrt
from time import perf_counter

from experiments.shared_multiplier_prefix import UNITS24, divisors


SCHEDULES = ('raw', 'wheel-in-raw', 'wheel-prefix')


def scan(n, lanes, height, schedule, reduced):
    if n <= 0 or lanes < 0 or height < 0 or schedule not in SCHEDULES:
        raise ValueError('expected positive product, nonnegative bounds and a known schedule')
    wheel = schedule != 'raw'
    if wheel and gcd(n, 6) != 1:
        raise ValueError('the mod-24 units wheel needs a product coprime to six')
    clock = perf_counter()
    work = dict(lane_roots=0, labels_visited=0, admitted=0, square_tests=0,
                contracted=0, excluded_by_lower_wheel=0, scale_gcds=0,
                scale_sieve_writes=0, hit_gcds=0, directly_tested_squares=0)
    square_part = [1] * (lanes + 1)
    if reduced:
        # At the end D is the largest integer such that D² divides this lane.
        for d in range(2, isqrt(lanes) + 1):
            for k in range(d*d, lanes + 1, d*d):
                square_part[k] = d
                work['scale_sieve_writes'] += 1
    windows = {}
    hits = {}
    factors = set()
    for k in range(1, lanes + 1):
        target = 4*k*n
        first = isqrt(target - 1) + 1
        work['lane_roots'] += 1
        residues = {((a + (k//a)*(n % 24))*v) % 24
                    for a in divisors(k) for v in UNITS24} if wheel else None
        s = first
        visited = 0
        while (visited < height if schedule == 'wheel-prefix' else s < first + height):
            work['labels_visited'] += 1
            if wheel and s % 24 not in residues:
                s += 1
                continue
            visited += 1
            work['admitted'] += 1
            scale = 1
            if square_part[k] > 1:
                work['scale_gcds'] += 1
                scale = gcd(square_part[k], s)
            if scale > 1:
                work['contracted'] += 1
                lane, label = k // (scale*scale), s // scale
                begin, end, lower_residues = windows[lane]
                if wheel and label % 24 not in lower_residues:
                    # Every square admits an orientation at its own lane.
                    work['excluded_by_lower_wheel'] += 1
                    root = None
                else:
                    if not begin <= label < end:
                        raise ArithmeticError('contracted label outside the earlier prefix')
                    lower_root = hits.get((lane, label))
                    root = None if lower_root is None else scale*lower_root
            else:
                work['square_tests'] += 1
                delta = s*s - target
                candidate = isqrt(delta)
                root = candidate if candidate*candidate == delta else None
                if root is not None:
                    work['directly_tested_squares'] += 1
            if root is not None:
                hits[k, s] = root
                for value in ((s + root)//2, (s - root)//2):
                    factor = gcd(value, n)
                    work['hit_gcds'] += 1
                    if 1 < factor < n:
                        factors.add(factor)
            s += 1
        windows[k] = first, s, residues
    return hits, factors, work, perf_counter() - clock


def compare(n, lanes, height, schedule):
    before, found, full, full_seconds = scan(n, lanes, height, schedule, False)
    after, factors, reduced, reduced_seconds = scan(n, lanes, height, schedule, True)
    if before != after or found != factors:
        raise ArithmeticError('the reduced and full searches disagree')
    if full['square_tests'] != reduced['square_tests'] + reduced['contracted']:
        raise ArithmeticError('a square-test row was neither tested nor contracted')
    return dict(squares=len(after), factors=sorted(factors), full=full, reduced=reduced,
                full_seconds=full_seconds, reduced_seconds=reduced_seconds)
