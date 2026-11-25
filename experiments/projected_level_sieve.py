"""Sieve consecutive trace levels in a positive, centered factor-remainder class."""

from collections import Counter
import json
from math import gcd, isqrt, prod
from statistics import median
from tempfile import TemporaryDirectory
from pathlib import Path
from time import perf_counter

from .centered_sum_quartic import centered_coordinates, windows
from .norm_auxiliary import integer_roots
from .projected_quartic_levels import ROOT, has_local_root, primitive_level, projected_relation
from scripts.factor import render_certificate, verify_file


BLOCK_BITS = 1 << 16
MAX_LEVELS = 1 << 30
PRIMES = tuple(p for p in range(7, 252) if all(p%d for d in range(2, isqrt(p)+1)))


def level_image(full, modulus, prime):
    """Bit j is set exactly when M*j*x²=F(x) has a nonzero x modulo prime."""
    coeffs = [a % prime for a in full]
    inv_modulus = pow(modulus, -1, prime)
    bits = 0
    for x in range(1, prime):
        value = 0
        for c in reversed(coeffs):
            value = (value*x+c) % prime
        j = value * inv_modulus * pow(x, -2, prime) % prime
        bits |= 1 << j
    return bits


def block_survivors(full, n, modulus, first, last, work, block_bits=BLOCK_BITS, primes=PRIMES):
    if block_bits < 1:
        raise ValueError('positive block size required')
    if first > last:
        return
    width = min(block_bits, last-first+1)
    tables = []
    for p in primes:
        if gcd(n*modulus, p) != 1:
            work['skipped_primes'] += 1
            continue
        image = level_image(full, modulus, p)
        # Repeat the p-bit period far enough to start at any of its p offsets.
        repeats = (width+2*p-2)//p
        repeated = image * (((1 << (repeats*p))-1)//((1 << p)-1))
        tables.append((p, repeated))
        work['unit_evaluations'] += p-1
        work['residues_in_images'] += bin(image).count('1')
        work['stored_period_bits'] += repeated.bit_length()
    work['image_tables'] = len(tables)
    work['peak_block_width'] = width
    for start in range(first, last+1, width):
        size = min(width, last-start+1)
        work['level_positions_covered'] += size
        work['blocks'] += 1
        mask = (1 << size)-1
        for p, table in tables:
            mask &= table >> (start % p)
            work['mask_intersections'] += 1
            work['logical_bits_intersected'] += size
            if not mask:
                work['empty_blocks'] += 1
                break
        while mask:
            lowest = mask & -mask
            yield start+lowest.bit_length()-1
            mask ^= lowest


def centered_search(n, radix, u=1, *, sieve=True, max_levels=MAX_LEVELS, block_bits=BLOCK_BITS):
    if radix < 8 or radix & (radix-1) or not 0 < u < radix or u % 2 == 0 or max_levels < 0:
        raise ValueError('expected a dyadic radix >= 8, odd residue and nonnegative level limit')
    low, high, center, sum_center, radius, s = windows(n)
    work = Counter()
    def coordinates(row):
        return centered_coordinates(row, n, center, sum_center, s)
    scales = [1, 2*s, radius, 2*s*s, 2*s*radius]
    start = perf_counter()
    trace, full, modulus, constant, spread, first, last = projected_relation(
        n, radix, u, coordinates, scales, work)
    reduction_seconds = perf_counter()-start
    count = max(0, last-first+1)
    last_checked = min(last, first+max_levels-1)
    processed = max(0, last_checked-first+1)
    hits = set()
    levels = (block_survivors(full, n, modulus, first, last_checked, work, block_bits) if sieve
              else range(first, last_checked+1))
    phase_start = perf_counter()
    remaining_seconds = 0.0
    first_survivors = []
    for j in levels:
        primitive_start = perf_counter()
        if len(first_survivors) < 16:
            first_survivors.append(j)
        work['primitive_polynomials'] += 1
        polynomial = primitive_level(trace, n, u, radix, j, modulus)
        for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
            work['primitive_modular_tests'] += 1
            if not has_local_root(polynomial, p):
                work['primitive_modular_rejections'] += 1
                break
        else:
            work['levels_isolated'] += 1
            for k in integer_roots(polynomial, -((u-low)//radix), (high-u)//radix, work):
                x = u+radix*k
                y, remainder = divmod(n, x)
                work['candidate_roots'] += 1
                if remainder == 0 and low <= y <= high:
                    hits.add(tuple(sorted((x,y))))
        remaining_seconds += perf_counter()-primitive_start
    phase_seconds = perf_counter()-phase_start
    if not sieve:
        work['level_positions_covered'] = processed
    groups = (radix//2+4*int(n%8 == 1))//2
    if work['level_positions_covered'] != processed:
        raise ArithmeticError('level scan accounting failed')
    return dict(n=str(n), radix=str(radix), u=str(u), positive=True, rank=4, level_sieve=sieve,
                factor_min=str(low), factor_max=str(high), modulus=str(modulus), spread=str(spread),
                constant=str(constant), trace=list(map(str, trace)), first_level=first, last_level=last,
                total_levels=count, unexamined_levels=count-processed, first_surviving_levels=first_survivors,
                total_positive_groups=str(groups), other_positive_groups=str(groups-1),
                pairs=[[str(x),str(y)] for x,y in sorted(hits)], work=dict(work),
                reduction_seconds=reduction_seconds, sieve_and_yield_seconds=phase_seconds-remaining_seconds,
                primitive_and_root_seconds=remaining_seconds, search_seconds=perf_counter()-start)


def matched(n, radix, u, repetitions):
    elapsed = {True: [], False: []}
    result = {}
    for i in range(repetitions):
        for mode in ((True,False) if i%2 == 0 else (False,True)):
            result[mode] = centered_search(n, radix, u, sieve=mode)
            elapsed[mode].append(result[mode]['search_seconds'])
    if any(r['unexamined_levels'] for r in result.values()) or result[True]['pairs'] != result[False]['pairs']:
        raise ArithmeticError('incomplete or inconsistent comparison')
    return dict(n=str(n), radix=str(radix), u=str(u), levels=result[True]['total_levels'],
                pairs=result[True]['pairs'], methods={
                    key:dict(median_seconds=median(elapsed[mode]), work=result[mode]['work'])
                    for mode,key in ((True,'periodic'),(False,'per-level'))})


def covered_centered_groups(n, radix, u):
    _, _, _, _, radius, s = windows(n)
    weight = prod((1, 2*s, radius, 2*s*s, 2*s*radius))
    e = 3
    while 3125*weight >= 12960 << (10*e):
        e += 1
    fine = 1 << e
    # If N/u is outside the coarse class, reciprocal swapping never joins two
    # lifts of u. This is true on all four large runs in the panel.
    count = fine//radix if fine >= radix and (n-u*u) % radix else None
    return dict(exact_quartic_exponent=e, distinct_fine_groups=count)


def run():
    cases = {row['id']:int(row['n']) for row in
             json.loads((ROOT/'benchmarks/quartic-factor-lanes.json').read_text())}
    names = ('unit-lane-crossed-2048', 'unit-lane-fresh-2048')
    controls = []
    with TemporaryDirectory() as temp:
        proof = Path(temp)/'Factorization.lean'
        for e in (604,600):
            for name in names:
                n = cases[name]
                r = centered_search(n, 1<<e)
                for pair in r['pairs']:
                    proof.write_text(render_certificate(n, list(map(int, pair))))
                    verify_file(proof)
                controls.append(dict(source=name, exponent=e, result=r, lean_certificates=len(r['pairs']),
                                     coverage=covered_centered_groups(n, 1<<e, 1),
                                     remaining_cofactor=None if r['pairs'] else str(n)))
    # The reference test constructs each primitive polynomial individually.
    comparisons = [matched(n, 8, 1, 3) for n in (3376036549, 2810005999)]
    comparisons += [matched(cases[name], 1<<e, 1, 3) for e in (609, 606) for name in names]
    return dict(primary_exponent=604, secondary_exponent=600, residue=1, block_bits=BLOCK_BITS,
                maximum_positions=MAX_LEVELS, auxiliary_primes=list(PRIMES), controls=controls,
                comparisons=comparisons)


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
