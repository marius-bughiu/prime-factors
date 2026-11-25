"""Count signed-gap candidates in a fixed number of intervals per oriented coordinate pair."""

import argparse
from collections import Counter
import json
from math import gcd, isqrt

from experiments.modular_hyperbola import Work, floor_sum, report_progression
from experiments.offset_winner_window import bounds, coordinate_range


def residues(low, high, modulus):
    """Half-open residue intervals for one closed interval of integers."""
    if high < low:
        return []
    length = high-low+1
    if length >= modulus:
        return [(0, modulus)]
    start = low % modulus
    stop = start+length
    if stop <= modulus:
        return [(start, stop)]
    return [(start, modulus), (0, stop-modulus)]


def gap_band(trace, width, product, tilted):
    """Return (a,b,L,U) with L <= b*abs(gap)-a*(S-trace) <= U, and root cost."""
    delta = trace*trace-product
    l = isqrt(delta)
    r = isqrt((trace+width)**2-product)
    if tilted and width:
        rise = r-l
        common = gcd(rise, width)
        a, b = rise//common, width//common
        assert a >= b
        constant = (a*a-b*b)*product
        ceiling = isqrt(constant-1)+1 if constant else 0
        cap = a*trace-ceiling
        return (a,b,b*l,cap), 2+int(constant != 0)
    return (0,1,l+(l*l < delta),r), 2


def block_filters(trace, length, product, residue, slope, modulus, tilted, trace_step=2):
    """Affine residue bounds for traces starting at trace with the given positive step."""
    band, cost = gap_band(trace, trace_step*(length-1), product, tilted)
    a,b,l,r = band
    if a:
        ranges = residues(l, r, b*modulus)
        filters = [(sign*b*slope-trace_step*a, sign*b*residue, b*modulus, ranges) for sign in (1,-1)]
        return filters, band, cost
    pieces = sorted(residues(l,r,modulus)+residues(-r,-l,modulus))
    merged = []
    for low, stop in pieces:
        if merged and low <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], stop))
        else:
            merged.append((low, stop))
    return [(slope, residue, modulus, merged)], band, cost


def exact_gaps(delta, residue, modulus, band, offset, result):
    """Try the explicitly lifted signed values when at most two fit in the band."""
    a, b, lower, upper = band
    low = max(0, (lower+a*offset+b-1)//b)
    high = (upper+a*offset)//b
    candidates = set()
    for left, right in ((low, high), (-high, -low)):
        first = left + (residue-left) % modulus
        if first > right:
            continue
        if first+2*modulus <= right:
            break
        candidates.add(first)
        if first+modulus <= right:
            candidates.add(first+modulus)
    else:
        if len(candidates) <= 2:
            result['gap_square_checks'] += len(candidates)
            return sorted(z for z in candidates if z*z == delta)
    result['fallback_roots'] += 1
    root = isqrt(delta)
    if root*root != delta:
        return []
    return sorted(z for z in {root,-root} if z % modulus == residue)


def count_progression(length, slope, intercept, modulus, low, stop, work):
    if stop-low == modulus:
        return length
    work.range_counts += 1
    return (floor_sum(length, modulus, slope, intercept-low, work)
            -floor_sum(length, modulus, slope, intercept-stop, work))


def candidate_counts(filters, size, work):
    """Count each sign separately. Their overlap bounds the distinct positions."""
    progressions = []
    counts = []
    for step, base, period, ranges in filters:
        step %= period
        base %= period
        count_for_sign = 0
        for low, end in ranges:
            count = count_progression(size, step, base, period, low, end, work)
            if count:
                count_for_sign += count
                progressions.append((step, base, period, low, end))
        counts.append(count_for_sign)
    return max(counts), min(size,sum(counts)), progressions


def unique_indices(progressions, size, work):
    """Stream positions from the sign progressions, coalescing overlaps."""
    seen = set()
    for step, base, period, low, end in progressions:
        for i, _ in report_progression(step, base, period, 0, size, low, end, work):
            if i not in seen:
                seen.add(i)
                yield i


def lifted_classes(n, t, s, v, first, length, divisor, split_only, unit_square, trace_units, work):
    from experiments.offset_gap_lift import affine_classes
    if not (trace_units and divisor > 1 and gcd(n,6) == 1):
        return affine_classes(n,t,s,v,first,length,divisor,work=work,split_only=split_only,
                              square8=unit_square == 8,square24=unit_square == 24,trace_units=trace_units)

    from experiments.offset_class_intersection import intersect_classes
    lifted = affine_classes(n,t,s,v,first,length,divisor,work=work)
    traces = affine_classes(n,t,s,v,first,length,1,work=work,trace_units=True)
    combined = intersect_classes(lifted,traces,work)
    if not split_only or not combined:
        return combined
    # The comparator tests exactly the same trace indices at original precision.
    _,_,_,base,slope,modulus = affine_classes(n,t,s,v,first,length,1,work=work)[0]
    return [(start, stride, size, (base+slope*start)%modulus, slope*stride%modulus, modulus)
            for start,stride,size,_,_,_ in combined]


def subintervals(length, parts):
    """Give more intervals to the sharply curved end near the first possible square."""
    parts = min(parts, length)
    for block in range(parts):
        start = block + (length-parts)*block**2//parts**2
        stop = block+1 + (length-parts)*(block+1)**2//parts**2
        yield start, stop


def scan_class(n, s, v, first, trace_step, length, shift, parts, intercept, slope, modulus,
               tilted, max_tests, result, work):
    """Accumulate interval bounds and tests on one disjoint progression of offsets."""
    k = s*v
    product = 4*n*k*k
    for start,stop in subintervals(length, parts):
        size = stop-start
        j0 = first+trace_step*start
        gap_residue = (intercept+slope*start)%modulus
        filters, band, roots = block_filters(j0+shift, size, product, gap_residue, slope, modulus, tilted, trace_step)
        result['bound_roots'] += roots
        largest, upper, progressions = candidate_counts(filters, size, work)
        result['intervals'] += 1
        result['empty_intervals'] += upper == 0
        result['candidate_lower'] += largest
        result['candidate_upper'] += upper
        if not upper:
            continue
        limit = min(max_tests-result['tested_positions'], upper)
        if not limit:
            result['untested_intervals'] += 1
            continue
        for rank, i in enumerate(unique_indices(progressions, size, work), start=1):
            if rank > limit:
                result['untested_intervals'] += 1
                break
            j = j0+trace_step*i
            result['tested_positions'] += 1
            if gcd(j,k) == 1:
                if 'coprime_tests' in result:
                    result['coprime_tests'] += 1
                trace = j+shift
                gap_class = (gap_residue+slope*i)%modulus
                for gap in exact_gaps(trace*trace-product, gap_class, modulus, band, trace_step*i, result):
                    p, rem = divmod(trace+gap, 2*s*s)
                    q, other = divmod(trace-gap, 2*v*v)
                    if not rem and not other and 1 < p < q and p*q == n:
                        result['hits'].append([j, k, str(p), str(q)])
            if rank == upper:
                break


def chart_window(n, box, s, v):
    shift = 2*box['T']*s*v
    first = max(1, isqrt(4*n*(s*v)**2-1)+1-shift)
    first += (s+v-first) % 2
    return shift, first, max(0, (box['J']-first)//2+1)


def chart(n, box, s, v, parts, *, max_tests=0, tilted=True, lift_cap=1, split_only=False,
          unit_square=1, trace_units=False):
    """Count a cover in O(parts) floor-sum queries per class, with a global position budget."""
    if (not 0 < v <= s or gcd(s, v) != 1 or min(parts,lift_cap) < 1 or max_tests < 0
            or unit_square not in (1,8,24) or trace_units and unit_square != 1):
        raise ValueError('expected ordered, positive, coprime coordinates and valid budgets')
    t = box['T']
    k = s*v
    shift, first, length = chart_window(n, box, s, v)
    work = Work()
    result = dict(s=s, v=v, parity_positions=length, intervals=0, empty_intervals=0,
                  candidate_lower=0, candidate_upper=0, tested_positions=0, untested_intervals=0, bound_roots=1,
                  gap_square_checks=0, fallback_roots=0, hits=[])
    if lift_cap == 1 and unit_square == 1 and not trace_units:
        modulus = 4*k*k
        projector = v*v*pow(v*v, -1, s*s)
        c = 1-2*projector
        slope = 2*c % modulus
        intercept = (s*s-v*v+c*(first+shift-s*s-v*v)) % modulus
        classes = [(0,1,length,intercept,slope,modulus)]
    else:
        from experiments.offset_gap_lift import choose_divisor
        setup_work = Counter()
        divisor = choose_divisor(k, lift_cap, work=setup_work)
        classes = lifted_classes(n,t,s,v,first,length,divisor,split_only,unit_square,trace_units,setup_work)
        result['lift_setup'] = dict(setup_work)
        result['divisor'] = divisor
        result['eligible_positions'] = sum(row[2] for row in classes)
        result['classes'] = len(classes)
        result['coprime_tests'] = 0
    for start,stride,count,residue,slope,modulus in classes:
        scan_class(n, s, v, first+2*start, 2*stride, count, shift, parts, residue, slope, modulus,
                   tilted, max_tests, result, work)
    result.update(range_counts=work.range_counts, euclidean_steps=work.euclidean_steps)
    return result


def sample_coordinates(box):
    """Four public trial directions. They cover only these coordinates."""
    t, lower, last = box['T'], box['L'], box['K']
    pairs = []
    for i in range(1,5):
        v = max(1, i*isqrt(last)//5)
        choices = coordinate_range(t, lower, last, v)
        s = (choices.start+choices.stop-1)//2
        while s > v and gcd(s,v) != 1:
            s -= 1
        if s in choices and gcd(s,v) == 1 and (s,v) not in pairs:
            pairs.append((s,v))
    return pairs


def coordinate_pairs(box, all_vectors):
    if not all_vectors:
        yield from sample_coordinates(box)
        return
    for v in range(1,isqrt(box['K'])+1):
        for s in coordinate_range(box['T'],box['L'],box['K'],v):
            if gcd(s,v) == 1:
                yield s,v


def search(n, parts, *, all_vectors=False, max_vectors, max_tests=0, tilted=True,
           lift_cap=1, split_only=False, unit_square=1, trace_units=False):
    if (n < 5 or n % 2 == 0 or isqrt(n)**2 == n or min(parts, max_vectors, lift_cap) < 1 or max_tests < 0
            or unit_square not in (1,8,24) or trace_units and unit_square != 1):
        raise ValueError('expected a positive search budget and an odd nonsquare input >= 5')
    box = bounds(n)
    pairs = coordinate_pairs(box, all_vectors)
    total = dict(vectors=0, parity_positions=0, intervals=0, empty_intervals=0, candidate_lower=0, candidate_upper=0,
                 tested_positions=0, untested_intervals=0, gap_square_checks=0, fallback_roots=0,
                 bound_roots=0, range_counts=0, euclidean_steps=0)
    divisors = Counter()
    setup_work = Counter()
    lifting = lift_cap > 1 or unit_square != 1 or trace_units
    if lifting:
        total.update(eligible_positions=0, classes=0, coprime_tests=0)
    found = []
    exhausted = False
    for pair in pairs:
        if total['vectors'] == max_vectors:
            break
        row = chart(n, box, *pair, parts, max_tests=max_tests-total['tested_positions'],
                    tilted=tilted, lift_cap=lift_cap, split_only=split_only,
                    unit_square=unit_square, trace_units=trace_units)
        if lifting:
            divisors[str(row['divisor'])] += 1
            setup_work.update(row['lift_setup'])
        total['vectors'] += 1
        for key in total:
            if key != 'vectors':
                total[key] += row[key]
        found.extend(row['hits'])
    else:
        exhausted = True
    if lifting:
        total.update(lift_cap=lift_cap, split_only=split_only, unit_square=unit_square, trace_units=trace_units,
                     divisors=dict(divisors), lift_setup=dict(setup_work))
    return dict(**total, hits=found, schedule_exhausted=exhausted, all_vectors=all_vectors,
                max_tests=max_tests, max_vectors=max_vectors, parts=parts, tilted=tilted)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--parts', type=int, default=16)
    parser.add_argument('--max-vectors', type=int, default=4)
    parser.add_argument('--max-tests', type=int, default=0)
    parser.add_argument('--horizontal', action='store_true')
    parser.add_argument('--lift-cap', type=int, default=1, help='largest divisor allowed for inverse lifting')
    rules = parser.add_mutually_exclusive_group()
    rules.add_argument('--unit-square', type=int, choices=(1,8,24), default=1,
                       help='use the identity for squares of units at the selected precision')
    rules.add_argument('--trace-units', action='store_true', help='use the possible factor residues modulo 24')
    parser.add_argument('--split-only', action='store_true', help='compare the original precision on the same subclasses')
    parser.add_argument('--all-vectors', action='store_true',
                        help='scan the coordinate range for balanced equal-width odd primes, smaller prime ≥ 17')
    args = parser.parse_args()
    print(json.dumps(search(args.n, args.parts, all_vectors=args.all_vectors,
                            max_vectors=args.max_vectors, max_tests=args.max_tests, tilted=not args.horizontal,
                            lift_cap=args.lift_cap, split_only=args.split_only, unit_square=args.unit_square,
                            trace_units=args.trace_units), indent=2))
