"""Compare a public root of 5 with ordinary local tests on the same sum interval."""

from heapq import merge
from itertools import combinations, islice
import json
from math import isqrt

from experiments.cyclotomic_sum_lift import _check_sum, _count, _positions
from scripts.factor import primes_through

# For each of these odd moduli, a sum is admissible iff its discriminant is a square.
MODULI = (7, 9, 11, 13, 25)
SQUARES = {m: frozenset(i*i % m for i in range(m)) for m in MODULI}


def _factor_bounds(n, bits):
    if bits < 2 or n % 2 == 0:
        raise ValueError("expected an odd product and a factor width >= 2")
    lo, hi = (1 << (bits-1))+1, (1 << bits)-1
    if not lo*lo <= n <= hi*hi:
        raise ValueError("product is outside the promised odd factor width")
    return lo, hi


def _setup(n, lo, hi):
    # Among lo+floor(n/lo), hi+floor(n/hi), the tighter endpoint is
    # selected before division via the sign of n-lo*hi.
    endpoint = lo if n <= lo*hi else hi
    midpoint = isqrt(n-1)+1
    upper = (endpoint+n//endpoint) & ~1
    stride = 4*(2 if n%4 == 3 else 1)*(3 if n%3 == 2 else 1)
    return midpoint, upper, stride


def _lanes(n, lower, upper, stride):
    # The unit pairs whose product is 4 mod 5 have possible sums 0, 1 and 4.
    residue = (n+1)%stride
    return [(s%5, _positions(lower, upper, s, 5*stride))
            for i in range(5) if (s := residue+stride*i)%5 in (0, 1, 4)]


def search(n, bits, max_tests, *, square_probe=True):
    """Run one search independently, with N, the promised width and a test cap."""
    if max_tests < 0:
        raise ValueError("expected a nonnegative discriminant cap")
    lo, hi = _factor_bounds(n, bits)
    work = dict(setup_roots=0, upper_divisions=0, square_probes=0, root=None, lower=None,
                upper=None, stride=None, stride_sites=None, before=None, survivors=None,
                discriminant_tests=0, unvisited=None, hit_sum=None)
    if n%5 != 4:
        return None, dict(work, outcome="outside_product_class")
    midpoint, upper, stride = _setup(n, lo, hi)
    lower = 2*midpoint
    lanes = _lanes(n, lower, upper, stride)
    work.update(root=midpoint, setup_roots=1, upper_divisions=1, stride=stride,
                lower=lower, upper=upper, stride_sites=_count(_positions(lower, upper, (n+1)%stride, stride)),
                before=sum(_count(lane) for _, lane in lanes))
    if square_probe:
        # N+5 is a square iff this existing boundary root squares to N+5 (N>=9).
        work['square_probes'] = 1
        if midpoint*midpoint != n+5:
            return None, dict(work, outcome="no_square")
        lanes = [(s, lane) for s, lane in lanes if s == 0]
    total_sites = sum(_count(lane) for _, lane in lanes)
    work.update(survivors=total_sites, unvisited=total_sites)
    for total in merge(*(lane for _, lane in lanes)):
        if work['discriminant_tests'] == max_tests:
            break
        work['discriminant_tests'] += 1
        work['unvisited'] -= 1
        factor = _check_sum(n, total)
        if factor is not None:
            return factor, dict(work, outcome="sum_square", hit_sum=total)
    return None, dict(work, outcome="test_cap" if work['unvisited'] else "exhausted")


def local_context(n, bits, cap):
    """Check a bounded prefix of the ordinary W+5 lanes with additional small moduli."""
    if n%5 != 4 or cap < 0:
        raise ValueError("expected product class four modulo five and a nonnegative cap")
    midpoint, upper, stride = _setup(n, *_factor_bounds(n, bits))
    lanes = _lanes(n, 2*midpoint, upper, stride)
    total = sum(_count(lane) for _, lane in lanes)
    sites = list(islice(merge(*(lane for _, lane in lanes)), cap))
    def passes(s, m):
        return (s*s-4*n)%m in SQUARES[m]
    individual = {str(m): [s for s in sites if passes(s, m)] for m in MODULI}
    return dict(sites=sites, unvisited=total-len(sites), individual=individual,
                through_11=[s for s in sites if all(passes(s, m) for m in (7, 9, 11))])


def census(first_bits=2, last_bits=11):
    """Order all distinct odd-prime pairs by common width, then by increasing product."""
    counts = []
    first = dict(selective=None, full_width=None, fewer_discriminants=None)
    for bits in range(first_bits, last_bits+1):
        primes = [p for p in primes_through((1 << bits)-1) if p >= 1 << (bits-1) and p%2]
        row = dict(bits=bits, pairs=0, probes=0, square_witnesses=0, selective=0, hits=[])
        for n, p in sorted((p*q, p) for p, q in combinations(primes, 2)):
            row['pairs'] += 1
            factor, work = search(n, bits, 100)
            row['probes'] += work['square_probes']
            if work['survivors'] is None:
                continue
            row['square_witnesses'] += 1
            if factor is None or factor != p:
                raise ValueError("square witness failed to split its pair within the census budget")
            row['hits'].append(n)
            if work['before'] < 2 or work['survivors'] != 1:
                continue
            row['selective'] += 1
            reference, ordinary = search(n, bits, 100, square_probe=False)
            if reference != factor:
                raise ValueError("ordinary and probe scans disagreed")
            for key, qualifies in [('selective', True), ('full_width', n.bit_length()==2*bits),
                                   ('fewer_discriminants', ordinary['discriminant_tests']>work['discriminant_tests'])]:
                if qualifies and first[key] is None:
                    first[key] = n
        counts.append(row)
    return dict(widths=counts, first=first)


if __name__ == "__main__":
    print(json.dumps(census(), indent=2))
