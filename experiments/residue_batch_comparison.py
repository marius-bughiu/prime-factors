"""Compare fixed and geometry-only allocations on complete prime populations."""
import argparse
from bisect import bisect_left, bisect_right
from collections import Counter
from functools import lru_cache
import json
from math import gcd

from .gap_coverage import primes_through
from .residue_batch_allocation import ALLOCATION
from .shared_multiplier_prefix import UNITS24, divisors, merge
from .shared_multiplier_selection import probe
from .two_interior_population import labels
from .weighted_partner_counts import partner_interval, preceding_distance


def limits(bits):
    if not 11 <= bits <= 26:
        raise ValueError('the bounded census supports 11 through 26 bits per prime')
    u = 1 << bits
    return u, [p for p in primes_through(u-1) if p >= u//2]


def partner_bounds(u, p):
    return max(p+1, (9*u*u+16*p-1)//(16*p)), min(u-1, 5*u*u//(8*p))


def search(n):
    """Return the three discoverable sets using only the product."""
    allocation = ALLOCATION[n%24]
    common, _ = probe(n, 1, labels(n, 1, 1, 16))
    fixed, adaptive = set(), set()
    for a,b,f,g in ((3,2,7,allocation[0]), (7,5,8,allocation[1])):
        seq = labels(n, a, b, max(f,g))
        both, _ = probe(n, a*b, seq[:min(f,g)])
        extra, _ = probe(n, a*b, seq[min(f,g):])
        fixed |= both
        adaptive |= both
        if f > g:
            fixed |= extra
        else:
            adaptive |= extra
    return common,fixed,adaptive


def summarize(counts):
    common = sum(v for (prefix,_,_),v in counts.items() if prefix)
    fixed = sum(v for (prefix,fixed,_),v in counts.items() if not prefix and fixed)
    adaptive = sum(v for (prefix,_,adaptive),v in counts.items() if not prefix and adaptive)
    return dict(products=sum(counts.values()), prefix=common, fixed_extra=fixed, adaptive_extra=adaptive,
                fixed_only=counts[False,True,False], adaptive_only=counts[False,False,True],
                neither=counts[False,False,False])


def result(bits, by_residue):
    counts = Counter()
    for group in by_residue.values():
        counts.update(group)
    return dict(prime_bits=bits, **summarize(counts),
                residues={str(r): summarize(by_residue[r]) for r in UNITS24})


def direct(bits):
    u, primes = limits(bits)
    by_residue = {r: Counter() for r in UNITS24}
    for p in primes:
        low,high = partner_bounds(u,p)
        for q in primes[bisect_left(primes,low):bisect_right(primes,high)]:
            n = p*q
            pre,f,g = search(n)
            if any(value != p for value in pre|f|g):
                raise ValueError('gcd disagrees with trial-sieved primes')
            by_residue[n%24][bool(pre),bool(f),bool(g)] += 1
    return result(bits,by_residue)


@lru_cache(maxsize=None)
def plan(pmod,qmod,lower_prime):
    residue = pmod*qmod%24
    h,k = ALLOCATION[residue]
    directions = []
    for a,b,count,arm in ((1,1,16,0),(3,2,7,1),(7,5,8,1),(3,2,h,2),(7,5,k,2)):
        g = gcd(a+b*residue,24)
        for A in divisors(a*b):
            B = a*b//A
            s = (A*pmod+B*qmod)%24
            if gcd(s,24) != g:
                continue
            d = preceding_distance(s,g,count)
            # Uniformly discard an orientation whose strict partner interval
            # misses p < q < 2p throughout the public factor-bit range.
            dist = max(B-A,A-2*B,0)*lower_prime - d
            if dist >= 0 and dist**2 >= 4*A*lower_prime*d:
                continue
            directions.append((A,B,d,arm))
    return directions


def census(bits):
    u, primes = limits(bits)
    rows = {r: [] for r in UNITS24}
    for q in primes:
        rows[q%24].append(q)
    by_residue = {r: Counter() for r in UNITS24}
    for p in primes:
        low,high = partner_bounds(u,p)
        if low > high:
            continue
        for r,row in rows.items():
            lo, hi = bisect_left(row,low), bisect_right(row,high)
            if lo == hi:
                continue
            windows = [[],[],[]]
            for A,B,d,arm in plan(p%24,r,u//2):
                l,h = partner_interval(p,A,B,d)
                l,h = max(l,row[lo]), min(h,row[hi-1])
                if l <= h:
                    windows[arm].append((l,h))
            events = Counter()
            for arm,parts in enumerate(windows):
                for l,h in merge(parts):
                    start = bisect_left(row,l,lo,hi)
                    end = bisect_right(row,h,start,hi)
                    events[start] ^= 1 << arm
                    events[end] ^= 1 << arm
            last = lo
            mask = 0
            counts = by_residue[(p*r)%24]
            for i in sorted(events):
                counts[bool(mask&1),bool(mask&2),bool(mask&4)] += i-last
                mask ^= events[i]
                last = i
            counts[bool(mask&1),bool(mask&2),bool(mask&4)] += hi-last
    return result(bits,by_residue)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bits',type=int,nargs='+')
    parser.add_argument('--direct',action='store_true')
    args = parser.parse_args()
    print(json.dumps([(direct if args.direct else census)(bits) for bits in args.bits],indent=2))
