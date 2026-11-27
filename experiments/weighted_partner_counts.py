"""Count prime partners of each smaller prime for the three 34-root schedules."""
import argparse
from bisect import bisect_left, bisect_right
from collections import Counter
from functools import lru_cache
import json
from math import gcd, isqrt
from time import perf_counter

from .gap_coverage import primes_through
from .shared_multiplier_prefix import UNITS24, divisors, merge


ARMS = ('ordinary', 'six', 'six_and_thirtyfive')
# Bits mark the common prefix and each continuation. The last two share a bit.
PREFIXES = ((1, 1, 16, 1), (1, 1, 33, 2), (3, 2, 16, 4),
            (3, 2, 7, 8), (7, 5, 8, 8))


def preceding_distance(residue, wheel_gcd, count):
    """Distance to the count-th strictly preceding admissible trace."""
    steps = [d for d in range(1, 25) if gcd(residue-d, 24) == wheel_gcd]
    cycles, index = divmod(count-1, len(steps))
    return cycles*24 + steps[index]


@lru_cache(maxsize=None)
def plans(pmod, qmod, lower_prime):
    """Each proper gcd splits p,q across two roots, in some orientation AB=k."""
    result = []
    for a, b, count, flag in PREFIXES:
        k = a*b
        wheel = gcd(a+b*pmod*qmod, 24)
        for A in divisors(k):
            B = k//A
            residue = (A*pmod + B*qmod) % 24
            if gcd(residue, 24) != wheel:
                continue
            d = preceding_distance(residue, wheel, count)
            # All partners have p<q<2p. The distance from Bq to Ap is
            # at least gap*p. If (gap*p-d)^2/(4Apd) >= 1 here, it only
            # increases for p >= lower_prime: gap - d/p is nondecreasing.
            gap = max(B-A, A-2*B, 0)
            margin = gap*lower_prime-d
            if margin >= 0 and margin*margin >= 4*A*lower_prime*d:
                continue
            result.append((A, B, d, flag))
    return tuple(result)


def partner_interval(p, A, B, d):
    """For S=Ap+Bq, the H-th preceding label S-d must be below 2√(ABpq).

    With S-d positive, squaring gives (Bq-Ap-d)² < 4Apd. Subtracting one
    before taking the integer root preserves strict endpoints.
    """
    ap = A*p
    radius = isqrt(4*ap*d - 1)
    center = ap+d
    return (center-radius+B-1)//B, (center+radius)//B


def scan_row(p, qmod, primes, lo, hi, lower_prime, work):
    """Count prime-list index intervals, merging orientations inside each arm."""
    windows = {flag: [] for flag in (1, 2, 4, 8)}
    for A, B, d, flag in plans(p % 24, qmod, lower_prime):
        qlo, qhi = partner_interval(p, A, B, d)
        work['interval_square_roots'] += 1
        qlo, qhi = max(qlo, primes[lo]), min(qhi, primes[hi-1])
        if qlo <= qhi:
            windows[flag].append((qlo, qhi))
    events = {lo: 0, hi: 0}
    for flag, intervals in windows.items():
        for left, right in merge(intervals):
            start = bisect_left(primes, left, lo, hi)
            end = bisect_right(primes, right, start, hi)
            work['prime_list_bisections'] += 2
            events[start] = events.get(start, 0) ^ flag
            events[end] = events.get(end, 0) ^ flag
    previous, flags = lo, 0
    counts = Counter()
    for i in sorted(events):
        if i > previous:
            counts[flags] += i-previous
        flags ^= events[i]
        previous = i
    return counts


def population(bits):
    if not 11 <= bits <= 26:
        raise ValueError('the bounded prime census supports 11 through 26 bits per prime')
    begin = perf_counter()
    U = 1 << bits
    primes = [p for p in primes_through(U-1) if p >= U//2]
    by_residue = {r: [] for r in UNITS24}
    for q in primes:
        by_residue[q % 24].append(q)
    count_start = perf_counter()
    work = dict(all_primes=len(primes), smaller_primes_with_partners=0,
                nonempty_residue_rows=0, interval_square_roots=0, prime_list_bisections=0)
    counts = Counter()
    for p in primes:
        # The bin depends only on p*q. Compare both product endpoints inclusively.
        low = max(p+1, (9*U*U + 16*p-1)//(16*p))
        high = min(U-1, 5*U*U//(8*p))
        if low > high:
            continue
        any_partners = False
        for qmod, row in by_residue.items():
            lo = bisect_left(row, low)
            hi = bisect_right(row, high, lo)
            work['prime_list_bisections'] += 2
            if lo == hi:
                continue
            any_partners = True
            work['nonempty_residue_rows'] += 1
            counts.update(scan_row(p, qmod, row, lo, hi, U//2, work))
        work['smaller_primes_with_partners'] += any_partners
    common = sum(v for mask, v in counts.items() if mask & 1)
    total = sum(counts.values())
    extra = {name: sum(v for mask, v in counts.items() if not mask & 1 and mask & bit)
             for name, bit in zip(ARMS, (2, 4, 8))}
    outcomes = {'/'.join(str(int(bool(mask & bit))) for bit in (2, 4, 8)): v
                for mask, v in sorted(counts.items()) if not mask & 1}
    return dict(prime_bits=bits, products=total, common_prefix_splits=common,
                additional_splits=extra, total_splits={k: common+v for k, v in extra.items()},
                unresolved={k: total-common-v for k, v in extra.items()},
                extra_outcomes=outcomes, work=work, sieve_seconds=count_start-begin,
                counting_seconds=perf_counter()-count_start)


def report(rows):
    return {
        'population': 'All primes U/2 <= p < q < U with 9 U²/16 <= p*q <= 5 U²/8, U=2^prime_bits.',
        'search': 'Each schedule uses 34 roots per product. The common 16 ordinary traces are followed by 17 ordinary, 16 at (3,2), or 7 at (3,2) and 8 at (7,5).',
        'census': 'Sieve both primes, then count exact inclusive partner intervals using binary search in each residue class modulo 24. All ordered factor orientations of each multiplier are checked for admission and feasibility. Sieve and counting times measure the census, independently of factor search.',
        'validation': 'Every reported count at 16 bits agrees with the independent direct enumeration in research/two-interior-population.json. tests/test_weighted_partner_counts.py checks exact equality at a strict endpoint, compares direct prime products on either side of interval boundaries, and samples the product bin at all four bit sizes.',
        'runs': rows,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bits', type=int, nargs='+')
    args = parser.parse_args()
    print(json.dumps(report([population(bits) for bits in args.bits]), indent=2))
