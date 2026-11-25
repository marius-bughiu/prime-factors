"""Count signed-gap candidates in a fixed number of intervals per oriented coordinate pair."""

import argparse
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


def block_filters(trace, length, product, residue, slope, modulus, tilted):
    """Affine progressions indexed by i; offset j increases by two per step."""
    width = 2*(length-1)
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
        ranges = residues(b*l, cap, b*modulus)
        filters = [(sign*b*slope-2*a, sign*b*residue, b*modulus, ranges) for sign in (1,-1)]
        return filters, (a,b,b*l,cap), 2+int(constant != 0)
    l += l*l < delta
    pieces = sorted(residues(l,r,modulus)+residues(-r,-l,modulus))
    merged = []
    for low, stop in pieces:
        if merged and low <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], stop))
        else:
            merged.append((low, stop))
    return [(slope, residue, modulus, merged)], (0,1,l,r), 2


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


def chart(n, box, s, v, parts, *, max_tests=0, tilted=True):
    """Count a cover with O(parts) floor-sum queries and test at most max_tests offsets."""
    if not 0 < v <= s or gcd(s, v) != 1 or parts < 1 or max_tests < 0:
        raise ValueError('expected ordered, positive, coprime coordinates and valid budgets')
    t, j_limit = box['T'], box['J']
    k = s*v
    shift = 2*t*k
    product = 4*n*k*k
    first = max(1, isqrt(product-1)+1-shift)
    first += (s+v-first) % 2
    length = max(0, (j_limit-first)//2+1)
    modulus = 4*k*k
    projector = v*v*pow(v*v, -1, s*s)
    c = 1-2*projector
    slope = (2*c) % modulus
    intercept = (s*s-v*v+c*(first+shift-s*s-v*v)) % modulus
    work = Work()
    result = dict(s=s, v=v, parity_positions=length, intervals=0, empty_intervals=0,
                  candidate_lower=0, candidate_upper=0, tested_positions=0, untested_intervals=0, bound_roots=1,
                  gap_square_checks=0, fallback_roots=0, hits=[])
    parts = min(parts, length)
    for block in range(parts):
        # Give more intervals to the sharply curved end near the first possible square.
        start = block + (length-parts)*block**2//parts**2
        stop = block+1 + (length-parts)*(block+1)**2//parts**2
        size = stop-start
        j0 = first+2*start
        gap_residue = (intercept+slope*start)%modulus
        filters, band, roots = block_filters(j0+shift, size, product, gap_residue, slope, modulus, tilted)
        result['bound_roots'] += roots
        progressions = []
        signed_count = 0
        largest = 0
        for step, base, period, ranges in filters:
            step %= period
            base %= period
            count_for_sign = 0
            for low, end in ranges:
                count = count_progression(size,step,base,period,low,end,work)
                if count:
                    count_for_sign += count
                    progressions.append((step,base,period,low,end))
            signed_count += count_for_sign
            largest = max(largest, count_for_sign)
        upper = min(size,signed_count)
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
        checked = set()
        more = False
        for step,base,period,low,end in progressions:
            for i,_ in report_progression(step,base,period,0,size,low,end,work):
                if i in checked:
                    continue
                if len(checked) == limit:
                    more = True
                    break
                checked.add(i)
                j = j0+2*i
                trace = j+shift
                delta = trace*trace-product
                result['tested_positions'] += 1
                if gcd(j,k) == 1:
                    for gap in exact_gaps(delta, (gap_residue+slope*i)%modulus, modulus, band, 2*i, result):
                        p, rem = divmod(trace+gap, 2*s*s)
                        q, other = divmod(trace-gap, 2*v*v)
                        if not rem and not other and 1 < p < q and p*q == n:
                            result['hits'].append([j, k, str(p), str(q)])
                if len(checked) == upper:
                    break
            if more or len(checked) == upper:
                break
        result['untested_intervals'] += more
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


def search(n, parts, *, all_vectors=False, max_vectors, max_tests=0, tilted=True):
    if n < 5 or n % 2 == 0 or isqrt(n)**2 == n or min(parts, max_vectors) < 1 or max_tests < 0:
        raise ValueError('expected a positive search budget and an odd nonsquare input >= 5')
    box = bounds(n)
    if all_vectors:
        pairs = ((s,v) for v in range(1,isqrt(box['K'])+1)
                 for s in coordinate_range(box['T'],box['L'],box['K'],v) if gcd(s,v) == 1)
    else:
        pairs = iter(sample_coordinates(box))
    total = dict(vectors=0, parity_positions=0, intervals=0, empty_intervals=0, candidate_lower=0, candidate_upper=0,
                 tested_positions=0, untested_intervals=0, gap_square_checks=0, fallback_roots=0,
                 bound_roots=0, range_counts=0, euclidean_steps=0)
    found = []
    exhausted = False
    for pair in pairs:
        if total['vectors'] == max_vectors:
            break
        row = chart(n, box, *pair, parts, max_tests=max_tests-total['tested_positions'], tilted=tilted)
        total['vectors'] += 1
        for key in total:
            if key != 'vectors':
                total[key] += row[key]
        found.extend(row['hits'])
    else:
        exhausted = True
    return dict(**total, hits=found, schedule_exhausted=exhausted, all_vectors=all_vectors,
                max_tests=max_tests, max_vectors=max_vectors, parts=parts, tilted=tilted)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--parts', type=int, default=16)
    parser.add_argument('--max-vectors', type=int, default=4)
    parser.add_argument('--max-tests', type=int, default=0)
    parser.add_argument('--horizontal', action='store_true')
    parser.add_argument('--all-vectors', action='store_true',
                        help='scan the coordinate range for balanced equal-width odd primes, smaller prime ≥ 17')
    args = parser.parse_args()
    print(json.dumps(search(args.n, args.parts, all_vectors=args.all_vectors,
                            max_vectors=args.max_vectors, max_tests=args.max_tests, tilted=not args.horizontal), indent=2))
