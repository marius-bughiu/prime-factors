"""Recover modular root classes by testing narrow intervals at multiples of N."""
import argparse
from collections import Counter
from heapq import merge
import json
from math import gcd, isqrt
from pathlib import Path
from time import process_time_ns

from experiments.affine_radix_holdout import draw_prime
from experiments.mixed_ratio_heights import jacobi
from experiments.offset_tangent_cover import cube_root
from experiments.signed_norm_arcs import possible, search as arc_search
from experiments.split_prime_holdout import certificate
from experiments.three_root_targets import menu
from scripts.factor import primes_through

ROOT = Path(__file__).resolve().parents[1]
SEED = b'rectangular-root-windows/v1'
WHEEL = 64
SCREEN = primes_through(31)[1:]
SQUARE = frozenset((x*x) % WHEEL for x in range(WHEEL))


def bounds(n, d):
    """Y ≤ B, |X| ≤ H for a Dirichlet representative of each modular root."""
    threshold = cube_root(abs(d)*n-1)+1
    b = max(n//threshold, isqrt(n)+1)
    h = n//(b+1)
    kmax = (abs(d)*b*b + (h*h if d < 0 else 0))//n
    return b, h, kmax


def ceiling_root(low, d):
    return 0 if low <= 0 else isqrt((low-1)//d)+1


def interval(n, d, k, b, h):
    total = k*n
    if d > 0:
        return max(1, ceiling_root(total, d)), min(b, isqrt((total+h*h)//d))
    return max(1, ceiling_root(total-h*h, -d)), min(b, isqrt(total//(-d)))


def candidate_bound(n, d):
    """Sum a public bound for each dyadic range of k using the minimum square spacing."""
    b, h, kmax = bounds(n, d)
    total = 0
    start = 1
    while start <= kmax:
        count = min(2*start-1, kmax) - start + 1
        low_y = max(1, ceiling_root(start*n - (h*h if d < 0 else 0), abs(d)))
        total += count*(1+h*h//(abs(d)*2*low_y))
        start *= 2
    return kmax, total


def primitive_classes(n, d):
    """Remainders modulo 64 of k admitting a point primitive at 2."""
    sign = 1 if d > 0 else -1
    inverse = pow(n, -1, WHEEL)
    return {(sign*(d*y*y-x*x)*inverse) % WHEEL
            for y in range(WHEEL) for x in range(WHEEL) if (x | y) & 1}


def targets(n, rule):
    if rule == 'one':
        return [1]
    if rule == 'signed':
        return menu(n, rule)
    raise ValueError('unknown target rule')


def multiplier_ratio(n, h, bits, scale=1024):
    """Round the maximum larger/smaller quotient of the two weights upwards."""
    if bits < 2 or not (1 << (2*bits-2)) <= n < (1 << (2*bits)):
        raise ValueError('product cannot have the specified common prime width')
    upper = (1 << bits)-1
    low_y = isqrt(n)
    if low_y <= h or h >= (1 << (bits-1)):
        raise ValueError('numerator cutoff must be smaller than both primes and the row denominator')
    numerator = scale*upper**2*(low_y+h)
    denominator = n*(low_y-h)
    return (numerator+denominator-1)//denominator - scale


def product_count_bound(limit, scale, excess):
    odd = (isqrt(limit)+1)//2
    even = isqrt(limit//4)
    return odd+even+(2*excess*odd**2+excess*even*(even+1))//(4*scale)


def weight_products(limit, scale, excess, work):
    """Merge sorted rows of odd or opposite-parity coprime weights."""
    def lane(a, first, last, multiplier):
        for b in range(first, last+1, 2):
            work['weight_pairs'] += 1
            if gcd(a,b)==1:
                yield multiplier*a*b

    lanes = []
    for multiplier in (1,4):
        step = 2 if multiplier == 1 else 1
        for a in range(1, isqrt(limit//multiplier)+1, step):
            work['small_weights'] += 1
            first = a if multiplier == 1 else a+1
            last = min(limit//(multiplier*a), (scale+excess)*a//scale)
            if first <= last:
                lanes.append(lane(a, first, last, multiplier))
    previous = 0
    for k in merge(*lanes):
        if k != previous:
            yield k
            previous = k


def run(n, ds, *, sieve=True, rows=None, per_row=None, stop=False, factor_bits=None):
    """Scan a product alone. Row zero for D=1 contains only trivial unit roots.

    Completeness for nonsquare targets is conditional on all prime divisors
    exceeding H, as in the balanced panel. When fixed caps apply, report the
    untouched rows and truncated candidate intervals.
    """
    if n < 7 or gcd(6, n) != 1 or isqrt(n)**2 == n:
        raise ValueError('expected a nonsquare product coprime to six')
    if any(d not in (-1, -2, -3, -6, 1, 2, 3, 6) for d in ds):
        raise ValueError('expected signed menu targets or the unit square')
    if (rows is not None and rows < 0) or (per_row is not None and per_row < 0):
        raise ValueError('expected nonnegative budgets')
    start = process_time_ns()
    work = Counter(dict(rows=0, rejected_rows=0, intervals=0, coordinates=0,
                        square_tests=0, squares=0, truncated_positions=0))
    roots = {d: {} for d in ds}
    first = first_cpu = factor = None
    boxes = {}
    for d in ds:
        b, h, kmax = bounds(n, d)
        boxes[d] = (b, h, kmax)
    if factor_bits is not None and ds != [1]:
        raise ValueError('weight products apply to the difference-of-squares target')
    for d in ds:
        b, h, kmax = boxes[d]
        classes = primitive_classes(n, d) if sieve else None
        excluded = [p for p in SCREEN if n % p and jacobi(d, p) == -1] if sieve else []
        limit = min(kmax, rows) if rows is not None else kmax
        if factor_bits is None:
            multipliers = range(1,limit+1)
        else:
            excess = multiplier_ratio(n,h,factor_bits)
            multipliers = weight_products(limit,1024,excess,work)
        for k in multipliers:
            work['rows'] += 1
            if sieve and ((k % WHEEL not in classes) or any(k % p == 0 for p in excluded)):
                work['rejected_rows'] += 1
                continue
            work['intervals'] += 1
            lo, hi = interval(n, d, k, b, h)
            if per_row is not None and hi-lo+1 > per_row:
                work['truncated_positions'] += hi-lo+1-per_row
                if d > 0:
                    hi = lo + per_row - 1
                else:
                    lo = hi - per_row + 1
            values = range(lo, hi+1) if d > 0 else range(hi, lo-1, -1)
            offset = -k*n if d > 0 else k*n
            for y in values:
                work['coordinates'] += 1
                square = d*y*y+offset
                if sieve and square % WHEEL not in SQUARE:
                    continue
                work['square_tests'] += 1
                x = isqrt(square)
                if x*x != square:
                    continue
                work['squares'] += 1
                divisor = gcd(n, y)
                if divisor == 1:
                    r = x*pow(y, -1, n) % n
                    if (r*r-d) % n:
                        raise ArithmeticError('invalid modular root')
                    key = min(r, n-r)
                    reference = 1 if d == 1 else next(iter(roots[d]), key)
                    divisor = gcd(key-reference, n)
                    roots[d].setdefault(key, [k, x, y])
                if 1 < divisor < n and factor is None:
                    first_cpu = process_time_ns()-start
                    factor = str(divisor)
                    first = dict(target=d, multiplier=k, x=str(x), y=str(y), rows=work['rows'],
                                 coordinates=work['coordinates'], square_tests=work['square_tests'])
                    if stop:
                        break
            if stop and factor is not None:
                break
        if stop and factor is not None:
            break
    return dict(factor=factor, first=first, first_cpu_ns=first_cpu, roots=roots, work=dict(work),
                row_limits={str(d): str(kmax) for d, (_, _, kmax) in boxes.items()},
                intervals_finished=not (stop and factor is not None) and work['truncated_positions']==0
                and all(rows is None or kmax<=rows for _, _, kmax in boxes.values()))


def small_check():
    pairs = checked = 0
    ps = [p for p in primes_through(79) if p > 3]
    for i, p in enumerate(ps):
        for q in ps[i+1:]:
            n = p*q
            ds = [1, *menu(n, 'signed')]
            if p <= max(bounds(n,d)[1] for d in ds):
                continue
            expected = {d: {min(r, n-r) for r in range(n) if (r*r-d) % n == 0}
                        for d in ds}
            expected[1].discard(1)
            for sieve in (False, True):
                result = run(n, ds, sieve=sieve)
                if int(result['factor']) not in (p, q) or not result['intervals_finished']:
                    raise ArithmeticError('complete search failed')
                assert all(set(result['roots'][d]) == expected[d] for d in ds)
                assert all(bounds(n,d)[1]+bounds(n,d)[0] < n for d in ds)
            pairs += 1
            checked += sum(map(len, expected.values()))
    return dict(products=pairs, root_classes=checked)


def panel():
    variants = [('one',True),('signed',True),('signed',False),('arc',True)]
    records = []
    for bits in (16, 20):
        sample = kept = 0
        while kept < 8:
            side_seed = SEED+b'/'+str(bits).encode()
            p, q = sorted(draw_prime(side, sample, bits=bits, seed=side_seed) for side in (b'p',b'q'))
            sample += 1
            n = p*q
            if p == q or n.bit_length()!=2*bits:
                continue
            kept += 1
            results = {}
            for i in range(len(variants)):
                shift = (i+sample) % len(variants)
                for method,sieve in variants[shift:]+variants[:shift]:
                    start = process_time_ns()
                    if method == 'arc':
                        possible.cache_clear()
                        result = arc_search(n, 'integer_arcs', domain='unit')
                        data = dict(first_cpu_ns=result['first_cpu_ns'], work=result['work'],
                                    first=result['first_work'], factor=result['factor'])
                    else:
                        result = run(n, targets(n,method), sieve=sieve)
                        data = {k:result[k] for k in ('first_cpu_ns','first','work','factor')}
                    elapsed = process_time_ns()-start
                    factor = int(data['factor'])
                    if factor not in (p,q):
                        raise ArithmeticError('incorrect split')
                    key = method if sieve else method+'_unfiltered'
                    first_time = data.pop('first_cpu_ns')
                    if key not in results:
                        results[key] = dict(data=data, times=[], first_times=[])
                    elif results[key]['data'] != data:
                        raise ArithmeticError('inconsistent replay')
                    results[key]['times'].append(elapsed)
                    results[key]['first_times'].append(first_time)
            records.append(dict(bits=bits, sample=sample-1, n=str(n), factors=[str(p),str(q)],
                                methods=results, certificate=certificate(n,(p,q))))
    return records


def full_size():
    inputs = json.loads((ROOT/'benchmarks/target-norm-multipliers.json').read_text())
    out = []
    for case in inputs:
        if case['status'] != 'partial':
            continue
        n = int(case['n'])
        methods = {}
        for rule in ('one','signed'):
            ds = targets(n,rule)
            for sieve in (False,True):
                start = process_time_ns()
                result = run(n,ds,sieve=sieve,rows=512,per_row=2)
                result['cpu_ns']=process_time_ns()-start
                result['candidate_upper_bound']=str(sum(candidate_bound(n,d)[1] for d in ds))
                methods[rule+('_screened' if sieve else '_raw')] = result
        out.append(dict(id=case['id'], n=str(n), methods=methods))
    return out


if __name__=='__main__':
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--output',type=Path)
    cli.add_argument('--check-small',action='store_true')
    args=cli.parse_args()
    checks=small_check()
    if args.check_small:
        print(checks)
    else:
        data=dict(seed=SEED.decode(), checks=checks, panel=panel(), full_size=full_size(),
                  timing='Four rotated CPU measurements including setup. First-factor and complete times recorded.')
        encoded=json.dumps(data,indent=2)+'\n'
        if args.output:
            args.output.write_text(encoded)
        else:
            print(encoded,end='')
