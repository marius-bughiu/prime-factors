"""Reuse weighted square tests ruled out by public endpoints after an ordinary miss."""

import argparse
from bisect import bisect_left, bisect_right
from collections import Counter
from functools import lru_cache
import json
from math import gcd, isqrt
from pathlib import Path

from .geometry_weight_menu import TABLE
from .residue_batch_comparison import limits
from .shared_multiplier_prefix import divisors
from .two_interior_population import offsets


def first(n, k):
    return 1 + isqrt(4*k*n-1)


def trace_list(n, a, b, start, count):
    return [start+i for i in offsets(a, b, n%24, start%24, count)]


def read(n, k, trace):
    discriminant = trace*trace - 4*k*n
    root = isqrt(discriminant)
    if root*root == discriminant:
        factor = gcd((trace+root)//2, n)
        if 1 < factor < n:
            return min(factor, n//factor), root
    return None, root


@lru_cache(maxsize=None)
def allocations(a, b, residue):
    k = a*b
    lane = gcd(a+b*residue, 24)
    return [(i, k//i) for i in divisors(k) if gcd(i+(k//i)*residue, 24) == lane]


def ceil_div(x, y):
    return (x+y-1)//y


def spans(n, a, b, lower, upper, start):
    """Potential traces, clipped separately for every allocation of a*b."""
    if lower > upper:
        return []
    ranges = []
    for i,j in allocations(a, b, n%24):
        lo_num = i*lower*lower + j*n
        hi_num = i*upper*upper + j*n
        if i*lower*lower >= j*n:
            smallest = ceil_div(lo_num, lower)
        elif i*upper*upper <= j*n:
            smallest = ceil_div(hi_num, upper)
        else:
            smallest = start
        largest = max(lo_num//lower, hi_num//upper)
        if smallest <= largest:
            ranges.append((smallest, largest))
    return ranges


def _search(n, prime_bits, details=False, comparison=True, ablation=False):
    """Both searches receive only the product and the common prime width."""
    if prime_bits < 2 or n <= 1 or gcd(n, 6) != 1:
        raise ValueError('expected a common prime width of at least 2 and a product coprime to 6')
    ordinary_start = first(n, 1)
    ordinary = trace_list(n, 1, 1, ordinary_start, 33)
    chosen = TABLE[n%24]
    common = set()
    for trace in ordinary[:16]:
        hit, last_root = read(n, 1, trace)
        if hit is not None:
            common.add(hit)

    limit = 1 << prime_bits
    lower = max(limit//2, ceil_div(n, limit-1))
    upper = ordinary_start//2
    upper -= upper*upper > n
    remaining_upper = min(upper, (ordinary[15]-last_root)//2) if not common else upper
    old_hits, new_hits = common.copy(), common.copy()
    skipped = static_skipped = 0
    per_arm = []
    for a,b,count in chosen:
        k = a*b
        start = first(n, k)
        seq = trace_list(n, a, b, start, count)
        allowed = spans(n, a, b, lower, remaining_upper, start)
        if ablation and not common:
            static_ranges = spans(n, a, b, lower, upper, start)
            static_skipped += sum(not any(x <= t <= y for x,y in static_ranges) for t in seq)
        kept = 0
        for trace in seq:
            retain = bool(common) or any(x <= trace <= y for x,y in allowed)
            # Replay the old search for comparison. Only 'retain' labels debit the new arm.
            factor = None
            if retain or comparison:
                factor,_ = read(n, k, trace)
            if factor is not None:
                old_hits.add(factor)
                if retain:
                    new_hits.add(factor)
            kept += retain
        skipped += count-kept
        per_arm.append(kept)
    ordinary_hits = common.copy()
    static_hits = old_hits.copy()
    for index,trace in enumerate(ordinary[16:] if comparison else ordinary[16:16+skipped]):
        factor,_ = read(n, 1, trace)
        if factor is not None:
            ordinary_hits.add(factor)
            if index < skipped:
                new_hits.add(factor)
            if ablation and index < static_skipped:
                static_hits.add(factor)
    if details:
        work = dict(residue=n%24, prime_bits=prime_bits, lower=str(lower),
                    upper=str(upper), upper_after_prefix=str(remaining_upper),
                    ordinary_last=str(ordinary[15]), last_root=str(last_root),
                    weighted_kept=per_arm, ordinary_extra=skipped,
                    prefix_found=sorted(map(str,common)),
                    new_found=sorted(map(str,new_hits)), roots_per_schedule=34)
        if ablation:
            work.update(bit_width_only_found=sorted(map(str,static_hits)), bit_width_only_extra=static_skipped)
        if comparison:
            work.update(old_found=sorted(map(str,old_hits)), ordinary_found=sorted(map(str,ordinary_hits)))
        return work
    if ablation:
        return common, old_hits, new_hits, ordinary_hits, skipped, static_hits, static_skipped
    return common, old_hits, new_hits, ordinary_hits, skipped


def compare(n, prime_bits, details=False):
    """Replay all schedules, sharing common roots across comparisons."""
    return _search(n, prime_bits, details, ablation=details)


def search(n, prime_bits):
    """Run just the endpoint-pruned schedule, taking exactly 34 integer roots."""
    return _search(n, prime_bits, details=True, comparison=False)


BINS = {'central': (9,10), 'upper': (14,15), 'all': (4,16)}


def census(bits, band):
    limit, primes = limits(bits)
    lo,hi = BINS[band]
    totals = Counter()
    examples = {}
    skipped_counts = Counter()
    for p in primes:
        q_min = max(p+1, ceil_div(lo*limit*limit, 16*p))
        q_max = min(limit-1, hi*limit*limit//(16*p))
        for q in primes[bisect_left(primes,q_min):bisect_right(primes,q_max)]:
            n = p*q
            prefix, old, new, ordinary, skipped, static, static_skipped = _search(n, bits, ablation=True)
            if any(z != p for z in old|new|ordinary):
                raise AssertionError('gcd differs from the trial-sieved smaller prime')
            totals['products'] += 1
            totals['prefix'] += bool(prefix)
            totals['old_splits'] += bool(old)
            totals['new_splits'] += bool(new)
            totals['ordinary_splits'] += bool(ordinary)
            totals['bit_width_only_splits'] += bool(static)
            totals['extra_conditioned_splits'] += bool(new and not static)
            totals['products_further_pruned_after_prefix'] += skipped > static_skipped
            totals['new_only_vs_ordinary'] += bool(new and not ordinary)
            totals['ordinary_only_vs_new'] += bool(ordinary and not new)
            totals['gains'] += bool(new and not old)
            totals['losses'] += bool(old and not new)
            skipped_counts[skipped] += 1
            if new and not old:
                examples.setdefault(str(n%24), [str(n),str(p),str(q)])
    return dict(bits=bits, bin=band, totals=dict(totals), extra_tests=dict(sorted(skipped_counts.items())),
                first_gains_by_remainder=examples)


def controls():
    fixture = Path(__file__).resolve().parents[1]/'benchmarks'/'interior-prime-family.json'
    return [dict(fixture=case['id'], **compare(int(case['n']),1024,True))
            for case in json.loads(fixture.read_text())]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits',type=int)
    parser.add_argument('--bin',choices=BINS,default='central')
    parser.add_argument('--controls',action='store_true')
    args = parser.parse_args()
    if args.controls:
        print(json.dumps(controls(), indent=2))
    elif args.bits:
        print(json.dumps(census(args.bits,args.bin), indent=2))
