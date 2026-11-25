"""Bound and scan the possible positive vector coordinates of a proper offset hit."""

import argparse
from collections import Counter
import json
from math import gcd, isqrt
from pathlib import Path
from statistics import median
from time import perf_counter

from experiments.complete_offset_search import (
    CONTROL_IDS, ROOT, render_census_certificate, search as raw_search, slot_count,
)
from scripts.factor import primes_through


def bounds(n, *, equal_width=True):
    """Assume n=p*q, 17<=p<q<=2*p, with equal prime bit widths if requested."""
    if n < 4:
        raise ValueError('expected n >= 4')
    t = isqrt(n)
    h = n-t*t
    j = isqrt(4*h//3)
    k = t*j//h+1 if h else 0
    if equal_width:
        bits = (n.bit_length()+1)//2
        cap = (1 << bits)-1
        lower = max(1 << (bits-1), (n+cap-1)//cap)
    else:
        lower = isqrt((n-1)//2)+1
    slots, steps = slot_count(t, h, j) if h else (0, 0)
    radius = isqrt(k)
    width = max(0, t-lower)
    upper = (width*(slots+j*radius)+4*lower*j*radius)//(2*lower)
    return dict(T=t, h=h, J=j, K=k, L=lower, raw_slots=slots,
                coordinate_visits_upper=upper, floor_sum_steps=steps)


def coordinate_range(t, lower, last, v):
    """All s>=v with s*v<=last and lower*(s-1)<t*v, for positive t,lower,v."""
    return range(v, min(last//v, (t*v+lower-1)//lower)+1)


def search(n, max_visits, *, equal_width=True):
    """Enumerate all hits up to a raw coordinate-visit budget; count repeated positions."""
    if max_visits < 0:
        raise ValueError('expected a nonnegative visit cap')
    limits = bounds(n, equal_width=equal_width)
    t, h = limits['T'], limits['h']
    work = dict(visited_pairs=0, coordinate_rows=0, coprime_vectors=0, coprime_slots=0,
                square_tests=0, square_hits=0, proper_hit_visits=0, proper_hits=0)
    hits = {}
    result = dict(**limits, **work, hits=[], exhaustive=False, factor=None,
                  remaining=n, next_coordinate=None, max_visits=max_visits,
                  unvisited_upper=limits['coordinate_visits_upper'],
                  equal_width=equal_width, status='partial')
    if h == 0:
        result.update(status='split', exhaustive=True, factor=t, remaining=t)
        return result
    for j in range(1, limits['J']+1):
        last = t*j//h+1
        for v in range(1, isqrt(last)+1):
            result['coordinate_rows'] += 1
            for s in coordinate_range(t, limits['L'], last, v):
                if result['visited_pairs'] == max_visits:
                    result['next_coordinate'] = [j, v, s]
                    result['unvisited_upper'] -= result['visited_pairs']
                    return result
                result['visited_pairs'] += 1
                if gcd(s, v) != 1:
                    continue
                result['coprime_vectors'] += 1
                k = s*v
                if gcd(j, k) != 1:
                    continue
                result['coprime_slots'] += 1
                delta = j*j+4*k*(t*j-h*k)
                if delta < 0:
                    continue
                result['square_tests'] += 1
                d = isqrt(delta)
                if d*d != delta:
                    continue
                result['square_hits'] += 1
                f = gcd(n, (j+2*t*k-d)//2)
                if not 1 < f < n:
                    continue
                result['proper_hit_visits'] += 1
                if (j, k) not in hits:
                    hits[j, k] = dict(j=j, k=k, d=d, factor=f)
                    result['hits'].append(hits[j, k])
                    result['proper_hits'] += 1
                if result['factor'] is None:
                    result.update(status='split', factor=f, remaining=n//f)
    result.update(exhaustive=True, unvisited_upper=0, status='split' if hits else 'exhausted')
    return result


def census(bits, witnesses=None):
    """Check every winner against a complete raw scan on distinct b-bit prime pairs."""
    primes = [p for p in primes_through((1 << bits)-1) if p >= 1 << (bits-1)]
    counts = Counter()
    for i, p in enumerate(primes):
        for q in primes[i+1:]:
            n = p*q
            run = search(n, 65_536)
            ref = raw_search(n, 65_536, exhaust=True)
            if (not run['exhaustive'] or ref['unvisited_pairs'] or
                    len(run['hits']) != ref['proper_hits'] or run['factor'] not in (p, q) or
                    any(hit['factor'] not in (p, q) for hit in run['hits'])):
                raise AssertionError(f'incomplete winner coverage at {n}')
            if witnesses is not None:
                witnesses.extend((n, run['T'], hit['j'], hit['k'], hit['d'], hit['factor'])
                                 for hit in run['hits'])
            counts['products'] += 1
            counts['unique_hits'] += len(run['hits'])
            counts['raw_square_tests'] += ref['integer_square_roots']
            for key in ('raw_slots', 'visited_pairs', 'square_tests', 'proper_hit_visits'):
                counts[key] += run[key]
    return dict(bits=bits, **counts)


def compare_timing(bits=(7, 8, 9), rounds=4):
    """Alternate deterministic complete scans, excluding product generation and certification."""
    products = []
    for b in bits:
        primes = [p for p in primes_through((1 << b)-1) if p >= 1 << (b-1)]
        products.extend(p*q for i, p in enumerate(primes) for q in primes[i+1:])
    samples = {'raw': [], 'window': []}
    for i in range(rounds):
        for method in (('window', 'raw') if i % 2 else ('raw', 'window')):
            start = perf_counter()
            if method == 'raw':
                for n in products:
                    raw_search(n, 65_536, exhaust=True)
            else:
                for n in products:
                    search(n, 65_536)
            samples[method].append(perf_counter()-start)
    return dict(products=len(products), rounds=rounds, seconds=samples,
                median_seconds={key: median(values) for key, values in samples.items()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--census', action='store_true')
    modes.add_argument('--controls', action='store_true')
    modes.add_argument('--timing', action='store_true')
    modes.add_argument('--n', type=int)
    parser.add_argument('--max-visits', type=int, default=64)
    parser.add_argument('--balanced-only', action='store_true')
    parser.add_argument('--census-certificate', type=Path)
    args = parser.parse_args()
    if args.census_certificate and not args.census:
        parser.error('--census-certificate requires --census')
    if args.census:
        witnesses = [] if args.census_certificate else None
        output = [census(bits, witnesses) for bits in (7, 8, 9)]
        if args.census_certificate:
            args.census_certificate.write_text(render_census_certificate(witnesses))
    elif args.timing:
        output = compare_timing()
    elif args.controls:
        rows = json.loads((ROOT/'benchmarks/grouped-norm.json').read_text())
        output = [dict(id=row['id'], **search(int(row['n']), args.max_visits,
                                              equal_width=not args.balanced_only))
                  for row in rows if row['id'] in CONTROL_IDS]
    else:
        output = search(args.n, args.max_visits, equal_width=not args.balanced_only)
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
