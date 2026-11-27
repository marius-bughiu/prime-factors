"""Check the three equal-root schedules and measure their factor intervals."""
from math import isqrt
from time import perf_counter

from experiments.shared_multiplier_prefix import bounds, interval, merge
from experiments.two_interior_population import labels, search


def new_positions(n):
    lower, upper = bounds(n)

    def window(a, b, count):
        omitted = labels(n, a, b, count+1)[-1]
        radius = isqrt(omitted*omitted-4*a*b*n-1)
        return interval(a, omitted, radius, lower, upper)

    common = window(1, 1, 16)

    def count(windows):
        intervals = merge([w for w in windows if w[0] <= w[1]])
        return sum(hi-lo+1-max(0, min(hi,common[1])-max(lo,common[0])+1) for lo,hi in intervals)

    return [count([window(1,1,33)]), count([window(3,2,16)]), count([window(3,2,7), window(7,5,8)])]


def two_interior_case(case, proof, agree, certify_split):
    n = int(case['n'])
    start = perf_counter()
    prefix, ordinary, single, joint = search(n)
    elapsed = perf_counter()-start
    positions = new_positions(n)
    hits = [sorted(str(f) for f in prefix|additional) for additional in (ordinary,single,joint)]
    work = dict(roots_per_schedule=34, shared_run_roots=60, diagnostic_roots=11,
                positions=[str(w) for w in positions], found=hits)
    agree(dict(id=case['id'], **case['checks']), work, case['checks'])
    factor = min(prefix|joint, default=None)
    return certify_split(case, proof, factor, elapsed, 'two_interior_batches', work)
