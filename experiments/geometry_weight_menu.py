"""Choose two distinct weighted sums using only the product residue and leading widths."""
import argparse
from bisect import bisect_left, bisect_right
from collections import Counter
from fractions import Fraction
from functools import lru_cache
import json
from math import gcd, isqrt
from pathlib import Path

from .residue_batch_allocation import ALLOCATION, lower_score, step
from .residue_batch_comparison import limits, partner_bounds, result as allocation_result
from .shared_multiplier_selection import probe
from .two_interior_population import labels
from .weighted_partner_counts import preceding_distance, partner_interval
from .shared_multiplier_prefix import UNITS24, divisors, merge


def candidates():
    return [(a,b) for a in range(2,64) for b in range(1,a)
            if 5*a < 8*b and gcd(a,b)==1]


def coefficient_fourth(a,b,r):
    return Fraction(b*step(a,b,r)**2,a**3)


def choose(r):
    # Width is increasing in the coefficient at either fixed positive count.
    # Keep only the best representative for each distinct multiplier.
    best = {}
    for a,b in candidates():
        score = coefficient_fourth(a,b,r)
        key = (-score,a,b)
        if a*b not in best or key < best[a*b]:
            best[a*b] = key
    ranked = sorted(best.values())
    if -ranked[1][0] <= Fraction(24**2, 64**2):
        raise ArithmeticError('the denominator cutoff needs to be extended')
    directions = sorted((a,b) for _,a,b in ranked[:2])
    left,right = directions
    scores = {h: lower_score(*left,r,h)+lower_score(*right,r,15-h) for h in range(1,15)}
    h = max(scores, key=lambda i:(scores[i],-i))
    if any(scores[i]+2 > scores[h] for i in scores if i!=h):
        raise ArithmeticError('fixed-point bounds did not certify a unique allocation')
    return (*left,h), (*right,15-h)


TABLE = {r: choose(r) for r in UNITS24}

def rule(r):
    h,k = ALLOCATION[r]
    return ((3,2,h),(7,5,k)), TABLE[r]


def search(n):
    """Compare both schedules from the product. Shared tests are reused."""
    baseline, selected = rule(n%24)
    both = (dict(((a,b),k) for a,b,k in baseline), dict(((a,b),k) for a,b,k in selected))
    discoveries = [set(),set()]
    common,_ = probe(n,1,labels(n,1,1,16))
    for a,b in both[0].keys()|both[1].keys():
        h,k = both[0].get((a,b),0),both[1].get((a,b),0)
        seq = labels(n,a,b,max(h,k))
        shared,_ = probe(n,a*b,seq[:min(h,k)])
        rest,_ = probe(n,a*b,seq[min(h,k):])
        discoveries[0].update(shared)
        discoveries[1].update(shared)
        discoveries[0 if h>k else 1].update(rest)
    return common,*discoveries


def window(n,a,b,h):
    z = labels(n,a,b,h+1)[-1]
    rad = isqrt(z*z-4*a*b*n-1)
    return (z-rad+2*a-1)//(2*a),(z+rad)//(2*a)


def geometry_flags(n,u):
    x,y = sorted(window(n,a,b,h) for a,b,h in TABLE[n%24])
    ordinary = window(n,1,1,16)
    lower = max(u//2, (n+u-2)//(u-1))
    upper = isqrt(n)
    def common(participants):
        return max([lower]+[l for l,_ in participants]) <= min([upper]+[h for _,h in participants])
    return (x[0]<lower or max(x[1],y[1])>upper, common((x,y)),
            common((x,ordinary)) or common((y,ordinary)))


def result(bits, counts):
    row = allocation_result(bits, counts)
    renames = {'fixed_extra':'previous_extra', 'adaptive_extra':'selected_extra',
               'fixed_only':'previous_only', 'adaptive_only':'selected_only'}
    for group in [row, *row['residues'].values()]:
        for old,new in renames.items():
            group[new] = group.pop(old)
    return row


def direct(bits):
    u,primes = limits(bits)
    counts = {r: Counter() for r in UNITS24}
    geometry = Counter()
    for p in primes:
        low,high = partner_bounds(u,p)
        for q in primes[bisect_left(primes,low):bisect_right(primes,high)]:
            n = p*q
            prefix,baseline,selected = search(n)
            if any(f != p for f in prefix|baseline|selected):
                raise ValueError('gcd disagrees with the trial-sieved prime pair')
            counts[n%24][bool(prefix),bool(baseline),bool(selected)] += 1
            clipped,overlap,prefix_overlap = geometry_flags(n,u)
            geometry['clipped'] += clipped
            geometry['weighted_overlap'] += overlap
            geometry['prefix_overlap'] += prefix_overlap
    row = result(bits,counts)
    row['direct_geometry'] = dict(geometry)
    return row


@lru_cache(maxsize=None)
def plans(pmod,qmod,minimum):
    r = pmod*qmod%24
    reference, selected = rule(r)
    entries = []
    for flag, schedule in enumerate((((1,1,16),),reference,selected)):
        for a,b,count in schedule:
            wheel = gcd(a+b*r,24)
            for A in divisors(a*b):
                B = a*b//A
                residue = (A*pmod+B*qmod)%24
                if gcd(residue,24) != wheel:
                    continue
                previous = preceding_distance(residue,wheel,count)
                # A root gcd can only distribute these two primes to different
                # sides. This test rejects orientations with no possible q<2p.
                gap = max(B-A,A-2*B,0)*minimum-previous
                if gap >= 0 and gap*gap >= 4*A*minimum*previous:
                    continue
                entries.append((flag,A,B,previous))
    return entries


def census(bits):
    u,primes = limits(bits)
    rows = {r: [] for r in UNITS24}
    for p in primes:
        rows[p%24].append(p)
    counts = {r: Counter() for r in UNITS24}
    for p in primes:
        low,high = partner_bounds(u,p)
        if high < low:
            continue
        for r,possible in rows.items():
            lo,hi = bisect_left(possible,low),bisect_right(possible,high)
            if lo == hi:
                continue
            parts = [[],[],[]]
            for flag,A,B,d in plans(p%24,r,u//2):
                x,y = partner_interval(p,A,B,d)
                left,right = max(possible[lo],x),min(possible[hi-1],y)
                if left <= right:
                    parts[flag].append((left,right))
            changes = Counter()
            for i,windows in enumerate(parts):
                for left,right in merge(windows):
                    changes[bisect_left(possible,left,lo,hi)] ^= 1 << i
                    changes[bisect_right(possible,right,lo,hi)] ^= 1 << i
            previous, active = lo, 0
            bucket = counts[(p*r)%24]
            for index in sorted(changes):
                bucket[bool(active&1),bool(active&2),bool(active&4)] += index-previous
                active ^= changes[index]
                previous = index
            bucket[bool(active&1),bool(active&2),bool(active&4)] += hi-previous
    return result(bits,counts)


def controls():
    fixture = Path(__file__).resolve().parents[1]/'benchmarks'/'interior-prime-family.json'
    rows = []
    for case in json.loads(fixture.read_text()):
        n = int(case['n'])
        u = 1 << 1024
        lower = max(u//2, (n+u-2)//(u-1))
        upper = isqrt(n)
        ordinary_low, ordinary_high = window(n, 1, 1, 16)

        def sites(schedule):
            intervals = []
            for a,b,count in schedule:
                left,right = window(n,a,b,count)
                left,right = max(lower,left),min(upper,right)
                if left <= right:
                    intervals.append((left,right))
            return sum(right-left+1-max(0,min(right, ordinary_high)-max(left, ordinary_low)+1)
                       for left,right in merge(intervals))

        previous, selected = rule(n%24)
        prefix, old, new = search(n)
        rows.append(dict(fixture=case['id'], eligible=9*u*u <= 16*n <= 10*u*u,
                         residue=n%24, previous_sites=str(sites(previous)),
                         selected_sites=str(sites(selected)), previous_found=sorted(prefix|old),
                         selected_found=sorted(prefix|new)))
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--direct',type=int,metavar='PRIME_BITS')
    parser.add_argument('--census',type=int,nargs='+',metavar='PRIME_BITS')
    parser.add_argument('--controls', action='store_true', help='replay existing 2048-bit controls')
    args = parser.parse_args()
    if args.direct:
        print(json.dumps(direct(args.direct),indent=2))
    elif args.census:
        print(json.dumps([census(bits) for bits in args.census],indent=2))
    elif args.controls:
        print(json.dumps(controls(), indent=2))
    else:
        for r,arms in TABLE.items():
            print(r,arms)
