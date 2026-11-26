"""Compare the exact interval union for a shared weighted-discriminant prefix."""
import argparse
from math import gcd, isqrt

MULTIPLIER = 21_621_600
CAP = 16
UNITS24 = (1,5,7,11,13,17,19,23)


def divisors(k):
    """Generate all positive divisors of the prescribed small multiplier."""
    low, high = [], []
    for a in range(1,isqrt(k)+1):
        b,rem = divmod(k,a)
        if rem == 0:
            low.append(a)
            if a != b:
                high.append(b)
    return low+high[::-1]


def merge(windows):
    result = []
    for lo,hi in sorted(windows):
        if result and lo <= result[-1][1]+1:
            result[-1] = (result[-1][0],max(hi,result[-1][1]))
        else:
            result.append((lo,hi))
    return result


def bounds(n):
    bits = (n.bit_length()+1)//2
    high = isqrt(n)
    low = max(1<<(bits-1), (n+(1<<bits)-2)//((1<<bits)-1))
    if low > high:
        raise ValueError('empty equal-width factor interval')
    return low,high


def interval(a, first_omitted, hull_root, lower, upper):
    """Inclusive integer preimage of a*d+b*n/d < first_omitted."""
    return max(lower, (first_omitted-hull_root+2*a-1)//(2*a)), min(upper,(first_omitted+hull_root)//(2*a))


def _common(n, k, weights, traces, first_omitted, lower, upper):
    target = 4*k*n
    root = isqrt(first_omitted**2-target-1)
    intervals = []
    rows = []
    largest = None
    weighted_positions = 0
    for a in weights:
        l,h = interval(a,first_omitted,root,lower,upper)
        if l <= h:
            width = h-l+1
            intervals.append((l,h))
            rows.append((a,l,h))
            weighted_positions += width
            if largest is None or width > largest['positions']:
                largest = dict(a=a,b=k//a,lower=l,upper=h,positions=width)
    merged = merge(intervals)
    hits = set()
    gcd_splits = set()
    widest_factors = set()
    squares = []
    work = dict(trace_square_tests=0, assignment_intervals=len(weights), hull_roots=1,
                root_orientations=0, candidate_divisions=0, exact_squares=0, split_gcds=0)
    for s in traces:
        delta = s*s-target
        d = isqrt(delta)
        work['trace_square_tests'] += 1
        if d*d != delta:
            continue
        squares.append((s,d))
        work['exact_squares'] += 1
        if (s+d)%2 != 0:
            raise ArithmeticError('integral discriminant root has wrong parity')
        g = gcd((s+d)//2,n)
        work['split_gcds'] += 1
        if 1 < g < n:
            gcd_splits.add(min(g,n//g))
        for a,l,h in rows:
            for num in ((s-d,s+d) if d else (s,)):
                work['root_orientations'] += 1
                p,rem = divmod(num,2*a)
                if rem == 0 and l <= p <= h and 1 < p < n:
                    work['candidate_divisions'] += 1
                    if n % p == 0:
                        hits.add(p)
                        if a == largest['a']:
                            widest_factors.add(p)
    return dict(intervals=merged, directions=len(weights), active_directions=len(rows), interval_rows=rows,
                overlapping_positions=weighted_positions-sum(h-l+1 for l,h in merged),
                positions=sum(h-l+1 for l,h in merged), widest=largest,
                factors=sorted(hits), gcd_splits=sorted(gcd_splits), widest_factors=sorted(widest_factors),
                squares=squares, work=work)


def _ordinary_traces(n, cap, local):
    first = isqrt(4*n-1)+1
    if not local:
        return list(range(first,first+cap)), first+cap
    if gcd(n,6) != 1:
        raise ValueError('ordinary mod-24 baseline needs N coprime to six')
    admissible = {(d+n*pow(d,-1,24))%24 for d in UNITS24}
    result = []
    s = first
    while len(result) <= cap:
        if s%24 in admissible:
            result.append(s)
        s += 1
    return result[:-1],result[-1]



def best_single(n, k, weights, first, cap, lower, upper):
    """Pick the widest single direction using its own 16 unit-compatible labels.

    The rule is public. Unit squares are one mod 24, so (a+bN)d ranges over
    residues determined by gcd(a+bN,24). Price the plan for all weights
    before testing just the winning weight's selected discriminants.
    """
    menus = {}
    chosen = None
    width = 0
    for a in weights:
        g = gcd(a+(k//a)*n,24)
        if g not in menus:
            allowed = {(g*r)%24 for r in UNITS24}
            labels = []
            t = first
            while len(labels) <= cap:
                if t%24 in allowed:
                    labels.append(t)
                t += 1
            omitted = labels.pop()
            hull = isqrt(omitted*omitted-4*k*n-1)
            menus[g] = labels,omitted,hull
        labels,omitted,hull = menus[g]
        l,h = interval(a,omitted,hull,lower,upper)
        if h-l+1 > width:
            width = h-l+1
            chosen = (a,labels,omitted)
    if chosen is None:
        return dict(positions=0, widest=None, gcd_splits=[], factors=[],
                    work=dict(trace_square_tests=0,exact_squares=0),plan_weights=len(weights),
                    plan_hull_roots=len(menus))
    a,labels,omitted = chosen
    result = _common(n,k,[a],labels,omitted,lower,upper)
    result.update(plan_weights=len(weights),plan_hull_roots=len(menus))
    return result

def search(n, k=MULTIPLIER, cap=CAP):
    """Test one shared prefix, then measure two independent ordinary k=1 comparisons."""
    if n < 3 or n%2 == 0 or k < 1 or cap < 1:
        raise ValueError('requires odd N >= 3, positive multiplier and a positive trace budget')
    lower,upper = bounds(n)
    weights = divisors(k)
    first = isqrt(4*k*n-1)+1
    shared = _common(n,k,weights,range(first,first+cap),first+cap,lower,upper)
    comparisons = {}
    for label,local in (('ordinary',False),('ordinary_mod24',True)):
        if local and gcd(n,6) != 1:
            continue
        s,omitted = _ordinary_traces(n,cap,local)
        comparisons[label] = _common(n,1,[1],s,omitted,lower,upper)
    if gcd(n,6) == 1:
        comparisons['widest_mod24'] = best_single(n,k,weights,first,cap,lower,upper)
    return dict(lower=lower,upper=upper,remaining_positions=upper-lower+1-shared['positions'],
                k=k, cap=cap,first_trace=first,first_omitted=first+cap,
                divisor_trial_divisions=isqrt(k),shared=shared,**comparisons)


if __name__ == '__main__':
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int)
    parser.add_argument('--k',type=int,default=MULTIPLIER)
    parser.add_argument('--cap',type=int,default=CAP)
    args = parser.parse_args()
    print(json.dumps(search(args.n,args.k,args.cap),indent=2))
