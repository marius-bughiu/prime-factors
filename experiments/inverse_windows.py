"""Search a dyadic factor box using geometry and buckets of modular inverses.

With --product N, only N and the chosen dimensions enter discovery. Without
--product, test every unordered distinct b-bit prime pair and compare complete
searches with odd trial division. Tables are shared across equal product words.
"""
import argparse
import json
from collections import defaultdict
from dataclasses import asdict, dataclass
from itertools import combinations
from math import isqrt
from time import perf_counter

if __package__:
    from .gap_coverage import primes_through
else:
    from gap_coverage import primes_through


@dataclass
class Work:
    geometric_cells: int = 0
    surviving_cells: int = 0
    geometric_rows: int = 0
    surviving_rows: int = 0
    modular_points: int = 0
    surviving_trial_odds: int = 0
    baseline_trial_odds: int = 0


def geometry(n, xbase, side):
    """Sorted prefix boxes whose odd endpoint product range contains n."""
    last = 2*xbase-1
    xmin, xmax = max(xbase+1, (n+last-1)//last), min(last, isqrt(n))
    for left in range((xmin//side)*side, xmax+1, side):
        lo, hi = max(xmin, left+1), min(xmax, left+side-1)
        lo, hi = lo | 1, (hi-1) | 1
        if hi < lo:
            continue
        ymin = max(left+1, (n+hi-1)//hi) | 1
        ymax = min(last, n//lo)
        if ymax >= ymin:
            yield left, (hi-lo)//2+1, range(ymin//side, ((ymax-1)|1)//side+1)


def inverse_seeds(modulus, side):
    stride = modulus//8 if modulus >= 64 and side <= modulus//8 else modulus
    return stride, [(x, pow(x, -1, modulus)) for x in range(1, stride, 2)]


def word_table(a, modulus, side, seeds):
    table = defaultdict(list)
    for x, inv in seeds:
        y = a*inv % modulus
        table[x//side, y//side].append((x,y))
    return table


def search(n, xbase, side, modulus, stride, table):
    work, pairs = Work(), []
    xmin = max(xbase+1, (n+2*xbase-2)//(2*xbase-1)) | 1
    xmax = min(2*xbase-1, isqrt(n))
    work.baseline_trial_odds = max(0, (xmax-xmin)//2+1)
    for left, odds, columns in geometry(n, xbase, side):
        work.geometric_rows += 1
        whole_x, shift = divmod(left, modulus)
        shift, canonical = divmod(shift, stride)
        offset = shift*stride
        yshift = (n % modulus)*offset % modulus
        row_exists = False
        for column in columns:
            work.geometric_cells += 1
            lower_y = column*side
            entries = table.get((canonical//side, ((lower_y+yshift) % modulus)//side), ())
            work.modular_points += len(entries)
            if entries:
                work.surviving_cells += 1
                row_exists = True
            for low_x, low_y in entries:
                x = whole_x*modulus + offset + low_x
                y = lower_y-lower_y%modulus+(low_y-yshift)%modulus
                if x <= y and x*y == n:
                    pairs.append([x,y])
        if row_exists:
            work.surviving_rows += 1
            work.surviving_trial_odds += odds
    return pairs, work


def dimensions(bits, side_bits, word_bits):
    if not 2 <= bits or not 1 <= side_bits <= min(bits-1, word_bits):
        raise ValueError("require b>=2 and 1<=side-bits<=min(b-1,word-bits)")
    return 1 << (bits-1), 1 << side_bits, 1 << word_bits


def trial_pairs(n, xbase):
    xmin = max(xbase+1, (n+2*xbase-2)//(2*xbase-1)) | 1
    xmax = min(2*xbase-1, isqrt(n))
    return [[x,n//x] for x in range(xmin,xmax+1,2) if n % x == 0]


def search_product(n, bits, side_bits, word_bits):
    if n <= 0 or n % 2 == 0:
        raise ValueError("the residue search requires a positive odd product")
    xbase, side, modulus = dimensions(bits, side_bits, word_bits)
    start = perf_counter()
    stride, seeds = inverse_seeds(modulus, side)
    table = word_table(n % modulus, modulus, side, seeds)
    prep_seconds = perf_counter()-start
    start = perf_counter()
    factors, work = search(n, xbase, side, modulus, stride, table)
    return dict(n=str(n), factor_pairs=factors, remaining=[] if factors else [str(n)],
                inversions=len(seeds), entries=len(seeds), prep_seconds=prep_seconds,
                bucket_seconds=perf_counter()-start, **asdict(work))


def exhaustive(bits, side_bits, word_bits):
    xbase, side, modulus = dimensions(bits, side_bits, word_bits)
    primes = [p for p in primes_through(2*xbase-1) if p >= xbase and p % 2]
    targets = defaultdict(list)
    for p, q in combinations(primes, 2):
        targets[p*q % modulus].append((p*q,p,q))
    start = perf_counter()
    stride, seeds = inverse_seeds(modulus, side)
    prep_seconds = perf_counter()-start
    totals = Work()
    tests = 0
    bucket_seconds = trial_seconds = 0.
    for word, cases in targets.items():
        start = perf_counter()
        table = word_table(word, modulus, side, seeds)
        prep_seconds += perf_counter()-start
        for n, p, q in cases:
            start = perf_counter()
            got, work = search(n, xbase, side, modulus, stride, table)
            bucket_seconds += perf_counter()-start
            start = perf_counter()
            trial = trial_pairs(n, xbase)
            trial_seconds += perf_counter()-start
            if got != [[p,q]] or got != trial:
                raise AssertionError((n, got, trial))
            for k, v in vars(work).items():
                setattr(totals, k, getattr(totals, k)+v)
            tests += 1
    return dict(bits=bits, side=side, modulus=modulus, products=tests,
                words=len(targets), inversions=len(seeds), entries_per_table=len(seeds),
                batch_table_products=len(seeds)*len(targets),
                unshared_table_products=len(seeds)*tests,
                prep_seconds=round(prep_seconds,5), bucket_seconds=round(bucket_seconds,5),
                trial_seconds=round(trial_seconds,5), **asdict(totals))


def verify_moments(word_bits, side_bits):
    """Enumerate odd words and every circular start. Check both factorial moments."""
    modulus, side = 1 << word_bits, 1 << side_bits
    if not 1 <= side_bits <= word_bits <= 10:
        raise ValueError("moment enumeration supports 1<=side-bits<=word-bits<=10")
    xs = range(1, side, 2)
    seeds = [pow(x, -1, modulus) for x in xs]
    mass = pairs = 0
    for a in range(1, modulus, 2):
        hist = [0]*modulus
        for inv in seeds:
            hist[a*inv % modulus] += 1
        count = sum(hist[:side])
        for start in range(modulus):
            mass += count
            pairs += count*(count-1)
            count += hist[(start+side) % modulus]-hist[start]
    size = (modulus//2)*modulus
    n = len(xs)
    assert mass*modulus == size*n*side
    assert pairs*modulus**2 == size*n*(n-1)*side**2
    return dict(words_and_starts=size, total_hits=mass, ordered_distinct_collisions=pairs)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bits", type=int, help="factor bit width")
    parser.add_argument("side_bits", type=int)
    parser.add_argument("word_bits", type=int)
    parser.add_argument("--product", type=int)
    parser.add_argument("--compare-trial", action="store_true",
                        help="time a complete odd trial scan on the same single product")
    parser.add_argument("--moments", action="store_true")
    args = parser.parse_args()
    if args.moments:
        result = verify_moments(args.word_bits, args.side_bits)
    elif args.product is None:
        result = exhaustive(args.bits, args.side_bits, args.word_bits)
    else:
        n = args.product
        result = search_product(n, args.bits, args.side_bits, args.word_bits)
        if args.compare_trial:
            start = perf_counter()
            trial = trial_pairs(n, 1 << (args.bits-1))
            result['trial_seconds'] = perf_counter()-start
            if sorted(result['factor_pairs']) != trial:
                raise AssertionError((n, result['factor_pairs'], trial))
    print(json.dumps(result))
