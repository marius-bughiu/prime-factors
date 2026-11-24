"""Compare raw and modular midpoint schedules on every p<q in [X,2X].

Use --budget B --cap indices for a common raw window j<B, or --cap squares
for the first B admissible offsets per root. Search receives only N, its
public 2:1 balance promise, and the maximum exponent. All runs include misses.
"""
import argparse
import json
from dataclasses import asdict, dataclass
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path
from statistics import median
from time import perf_counter

if __package__:
    from .gap_coverage import primes_through
else:
    from gap_coverage import primes_through


def wheel(period, offsets):
    offsets = tuple(offsets)
    starts = []
    index = 0
    for phase in range(period):
        if index < len(offsets) and offsets[index] < phase:
            index += 1
        starts.append(index)
    return offsets, tuple(starts)


def build_wheels():
    square24 = {c*c % 24 for c in range(24)}
    external, combined = {}, {}
    for n in range(24):
        if gcd(n, 6) != 1:
            continue
        external[n] = wheel(24, (h for h in range(24) if (h*h-n) % 24 in square24))
        shapes = ((0,), (1, 4), (2, 3), (0, 1, 4), (0, 2, 3))
        for s, digits in enumerate(shapes):
            combined[n, s] = wheel(120, (t for t in range(120)
                                   if t % 24 in external[n][0] and t % 5 in digits))
    return external, combined


INVERSE5 = (0, 1, 3, 2, 4)
# At v=0 the possible h mod 5 with h²-N a *nonzero* square are {±s}.
INITIAL_SHAPE = (None, 0, 1, 2, 0)
INITIAL_INCLUSIVE = (None, 3, 1, 2, 4)
MODES = ('raw', 'external', 'ordinary120', 'inclusive', 'combined')


@dataclass
class Work:
    squares: int = 0
    root_lookups: int = 0
    hensel_digits: int = 0
    branches: int = 0
    wheel_rotations: int = 0
    center_extractions: int = 0
    table_entries_read: int = 0


def positions(period, table, phase, budget, limit, work):
    """Emit sorted j>=0 with j+phase in the wheel through the allowed horizon."""
    phase %= period
    allowed, starts = table
    index = starts[phase]
    base = -phase
    for _ in range(budget):
        if index == len(allowed):
            base += period
            index = 0
        work.table_entries_read += 1
        j = base + allowed[index]
        if j >= limit:
            break
        yield j
        index += 1


def search(n, exponent, budget, mode, cap, wheels, exhaustive_valuations=False):
    if n < 7 or gcd(n, 30) != 1:
        raise ValueError("expected an odd input coprime to 30")
    if exponent < 0 or budget < 1 or mode not in MODES or cap not in ('indices', 'squares'):
        raise ValueError("invalid exponent, budget, wheel, or cap")
    start, upper = isqrt(n-1) + 1, isqrt(9*n//8)
    work = Work()
    root, precision = 0, 1
    modulus = 1
    external, combined = wheels
    for v in range(exponent+1):
        # If the final exponent is a budget rather than a proved bound, assign
        # all higher valuations to it by also admitting the zero residue.
        allow_zero = mode == 'inclusive' or (v == exponent and not exhaustive_valuations)
        if v == 0:
            branches = [(start, 0)]
        else:
            modulus *= 25
            if precision == 1:
                work.root_lookups += 1
                if n % 5 not in (1, 4):
                    break
                root, precision = (1 if n % 5 == 1 else 2), 5
            while precision < modulus:
                digit = ((n-root*root)//precision) * INVERSE5[2*root % 5] % 5
                root += precision * digit
                precision *= 5
                work.hensel_digits += 1
            branches = sorted((start + (sign*root-start) % modulus, sign) for sign in (1, -1))
            if branches[0][0] > upper:
                break  # Every deeper root is contained in a current root class.
            if mode in ('combined', 'inclusive'):
                digit = ((n-root*root)//precision) * INVERSE5[2*root % 5] % 5
                root += precision * digit
                precision *= 5
                work.hensel_digits += 1

        for h, sign in branches:
            if h > upper:
                continue
            work.branches += 1
            limit = (upper-h)//modulus + 1
            if cap == 'indices':
                limit = min(limit, budget)
            if mode == 'raw':
                indices = range(min(budget, limit))
            else:
                work.wheel_rotations += 1
                if mode == 'external' or (mode == 'ordinary120' and v > 0):
                    indices = positions(24, external[n % 24], h, budget, limit, work)
                else:
                    if v == 0:
                        initial = INITIAL_SHAPE if mode == 'combined' and not allow_zero else INITIAL_INCLUSIVE
                        shape, phase = initial[n % 5], h
                    else:
                        # The sign gives the lifted root over this particular branch.
                        work.center_extractions += 1
                        center = ((sign*root-h) % precision)//modulus
                        inv = INVERSE5[2*h % 5]
                        shape = min(inv, 5-inv)
                        if allow_zero:
                            shape += 2
                        b = h % 24
                        phase = b + 24*((b+center) % 5)
                    indices = positions(120, combined[n % 24, shape], phase, budget, limit, work)
            for j in indices:
                midpoint = h + modulus*j
                delta = midpoint*midpoint - n
                d = isqrt(delta)
                work.squares += 1
                if d*d == delta:
                    return midpoint-d, work
    return None, work


def covered_by_rank(p, q, budget, mode):
    """Independent oracle on a known pair, used only after a search."""
    n, midpoint, half_gap = p*q, (p+q)//2, (q-p)//2
    start = isqrt(n-1)+1
    m = 1
    while half_gap % m == 0:
        modulus = m*m
        if mode != 'combined' or half_gap % (5*m):
            j = (midpoint-start)//modulus
            h = midpoint-modulus*j
            rank = 0
            for k in range(j+1):
                delta = (h+modulus*k)**2-n
                external = delta % 24 in (0, 1, 4, 9, 12, 16)
                if mode == 'raw':
                    allowed = True
                elif mode == 'external':
                    allowed = external
                elif mode == 'ordinary120':
                    allowed = external and delta % 5 in (0, 1, 4)
                else:
                    digit = (delta//modulus) % 5
                    allowed = external and digit in ((1, 4) if mode == 'combined' else (0, 1, 4))
                rank += allowed
                if rank > budget:
                    break
            if rank <= budget:
                return True
        m *= 5
    return False


def measure(x, budget, cap, verify=False):
    if x < 16 or budget < 1 or cap not in ('indices', 'squares'):
        raise ValueError("expected X>=16, B>=1 and cap equal to indices or squares")
    primes = [p for p in primes_through(2*x) if p >= x]
    exponent = 0
    while 5**(exponent+1) <= x//2:
        exponent += 1
    start = perf_counter()
    wheels = build_wheels()
    build_seconds = perf_counter()-start
    totals = {}
    for mode in MODES:
        totals[mode] = dict(hits=0, misses=0, squares_on_misses=0, seconds=0.0,
                            **asdict(Work()))
    for p, q in combinations(primes, 2):
        n = p*q
        factors = []
        for mode, counts in totals.items():
            start = perf_counter()
            factor, work = search(n, exponent, budget, mode, cap, wheels, exhaustive_valuations=True)
            counts['seconds'] += perf_counter()-start
            if factor is not None and factor != p:
                raise AssertionError((p, q, mode, factor))
            if verify and cap == 'squares' and bool(factor) != covered_by_rank(p, q, budget, mode):
                raise AssertionError((p, q, mode, "wrong rank in the true class"))
            counts['hits'] += factor is not None
            counts['misses'] += factor is None
            counts['squares_on_misses'] += work.squares if factor is None else 0
            for key, value in vars(work).items():
                counts[key] += value
            factors.append(factor)

        # Check the raw optimum directly from the unique exact valuation.
        d = (q-p)//2
        m = 1
        while d % (m*5) == 0:
            m *= 5
        distance = (p+q)//2 - (isqrt(n-1)+1)
        expected = p if distance < budget*m*m else None
        if factors[0] != expected:
            raise AssertionError((p, q, factors, expected))
        if cap == 'indices' and factors != [expected]*len(MODES):
            raise AssertionError((p, q, factors, "different coverage in the same window"))
        if cap == 'squares' and list(map(bool, factors)) != sorted(map(bool, factors)):
            raise AssertionError((p, q, factors, "lost a hit at equal square cap"))
    for counts in totals.values():
        counts['seconds'] = round(counts['seconds'], 4)
    return dict(x=x, prime_count=len(primes), pairs=len(primes)*(len(primes)-1)//2,
                cap=cap, budget=budget, maximum_exponent=exponent, methods=totals,
                table_setup=dict(seconds=round(build_seconds, 6), small_squares=24,
                                 external_tests=192, combined_tests=4800,
                                 external_entries=sum(len(t[0]) for t in wheels[0].values()),
                                 combined_entries=sum(len(t[0]) for t in wheels[1].values()),
                                 phase_entries=sum(len(t[1]) for tables in wheels for t in tables.values())))


def fixture_runs(budget, cap):
    path = Path(__file__).resolve().parents[1] / 'benchmarks' / 'gap-stride.json'
    wheels = build_wheels()
    rows = []
    for case in json.loads(path.read_text()):
        n = int(case['n'])
        for mode in MODES:
            elapsed = []
            for _ in range(3):
                start = perf_counter()
                found, work = search(n, case['max_exponent'], budget, mode, cap, wheels)
                elapsed.append(perf_counter()-start)
            factors = [str(found), str(n//found)] if found else []
            if found and (found <= 1 or n % found or (case['factors'] and factors != case['factors'])):
                raise AssertionError((case['id'], mode, factors))
            rows.append(dict(id=case['id'], mode=mode, cap=cap, budget=budget, factors=factors,
                             remaining=[] if found else [str(n)], median_seconds=median(elapsed),
                             **asdict(work)))
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('x', type=int, nargs='?')
    parser.add_argument('--gap-fixtures', action='store_true',
                        help='run three timed repetitions on each pinned 2048-bit gap fixture')
    parser.add_argument('--budget', default=8, type=int)
    parser.add_argument('--cap', choices=('indices', 'squares'), default='squares')
    parser.add_argument('--verify', action='store_true',
                        help='check surviving-position ranks independently on each known pair')
    args = parser.parse_args()
    if (args.x is not None) == args.gap_fixtures:
        parser.error('supply either X or --gap-fixtures')
    result = (fixture_runs(args.budget, args.cap) if args.gap_fixtures
              else measure(args.x, args.budget, args.cap, args.verify))
    print(json.dumps(result, indent=2))
