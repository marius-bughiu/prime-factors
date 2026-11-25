"""Search several short offset fractions in each partial projective CRT tuple."""

import argparse
from collections import Counter
from itertools import product
from math import gcd, isqrt, prod
import json
from pathlib import Path
from tempfile import TemporaryDirectory
from statistics import median
from time import perf_counter

from experiments.complete_offset_search import slot_count
from experiments.offset_crt_reconstruction import search as full_wheel_search
from experiments.offset_dyadic_search import chart_directions, select_charts
from experiments.offset_prime_power_slopes import local_directions, normalized_line
from experiments.grouped_offset_rows import local_failures
from experiments.offset_crt_wheel import choose_wheel
from experiments.short_basis_sieve import reduced_lattice_basis
from scripts.factor import primes_through, render_certificate, verify_file


ROW_PRIMES = primes_through(31)


def ceil_div(a, b):
    return -(-a//b)


def line_basis(primes, slopes, j_limit, k_limit, work):
    """Construct a reduced oriented basis (j,k), square-scaling the rectangular box."""
    entries = [(1,0) if r is None else (r,1) for r in slopes]
    return direction_basis(primes,entries,j_limit,k_limit,work)


def direction_basis(moduli, directions, j_limit, k_limit, work):
    infinity,modulus,a = normalized_line(moduli,directions)
    # The existing reducer returns (v,j), j = a*v modulo modulus and k = infinity*v.
    left, right = reduced_lattice_basis(modulus, a, lambda z:(k_limit*z[1], j_limit*infinity*z[0]), work)
    x, y = (left[1],infinity*left[0]), (right[1],infinity*right[0])
    if x[0]*y[1]-x[1]*y[0] < 0:
        y = (-y[0],-y[1])
    assert x[0]*y[1]-x[1]*y[0] == modulus*infinity
    left_scaled = (k_limit*x[0],j_limit*x[1])
    right_scaled = (k_limit*y[0],j_limit*y[1])
    first_norm = sum(v*v for v in left_scaled)
    assert first_norm <= sum(v*v for v in right_scaled)
    assert 2*abs(sum(v*w for v,w in zip(left_scaled,right_scaled))) <= first_norm
    return x,y


def row_interval(x, y, u, j_limit, k_limit, t, h):
    """All integer w with (j,k)=w*x+u*y in the actual triangular search region."""
    a,b = x
    c,d = y
    # Each pair means coefficient*w >= constant.
    limits = [(a,1-c*u),(-a,c*u-j_limit),(b,1-d*u),(-b,d*u-k_limit),
              (t*a-h*b,(h*d-t*c)*u-h)]
    lower = upper = None
    for coefficient, constant in limits:
        if coefficient > 0:
            value = ceil_div(constant, coefficient)
            lower = value if lower is None else max(lower,value)
        elif coefficient < 0:
            value = constant//coefficient
            upper = value if upper is None else min(upper,value)
        elif constant > 0:
            return 1,0
    return lower,upper


def batch_events(x,y,j_limit,k_limit,t,h,*,row_sieve=False,work=None):
    """Yield row starts and candidates separately so either kind of work is budgeted."""
    a,b = x
    c,d = y
    det = a*d-b*c
    # u=det(x,(j,k))/det. These bounds enclose the rectangle, including its edges.
    first = ceil_div(min(0,a*k_limit)-max(0,b*j_limit),det)
    last = (max(0,a*k_limit)-min(0,b*j_limit))//det
    obstructions = ()
    if row_sieve:
        pivot = a*a+4*b*(t*a-h*b)
        bound = max(abs(first),abs(last))
        base,powers = local_failures(pivot,ROW_PRIMES,bound)
        obstructions = base+powers
        if work is not None and pivot:
            work['pivot_prime_tests'] += sum(p<=bound for p in ROW_PRIMES)
    for u in range(first,last+1):
        rejected = False
        for q in obstructions:
            if work is not None:
                work['row_divisibility_tests'] += 1
            if u%q==0:
                rejected = True
                break
        yield 'row', rejected
        if rejected:
            continue
        lo,hi = row_interval(x,y,u,j_limit,k_limit,t,h)
        if u == 0:
            # A multiple of the first basis vector can be primitive only with coefficient ±1.
            values = (w for w in (-1,1) if lo<=w<=hi)
        else:
            values = range(lo,hi+1)
        for w in values:
            yield 'point', (a*w+c*u, b*w+d*u)


def search(n, max_batches, *, drop=1, max_events=1_000_000, exhaust=False, row_sieve=True,
           dyadic_exponent=None):
    """Drop the largest selected wheel primes; test them on the reconstructed points instead."""
    if not 4 <= n < 2**2048 or min(max_batches,drop,max_events)<0:
        raise ValueError('expected a target below 2^2048 and nonnegative budgets')
    if dyadic_exponent is not None and not 1 <= dyadic_exponent <= 20:
        raise ValueError('expected dyadic exponent in 1..20')
    t = isqrt(n)
    h = n-t*t
    j_limit = isqrt(4*h//3)
    result = dict(status='partial',factor=None,remaining=n,first_hit=None,raw_slots=0,full_tuples=0,
                  batch_primes=[],deferred_primes=[],total_batches=0,started_batches=0,completed_batches=0,
                  unfinished_batches=0,gauss_iterations=0,rows=0,rejected_rows=0,pivot_prime_tests=0,
                  row_divisibility_tests=0,point_visits=0,primitive_points=0,
                  deferred_checks=0,deferred_survivors=0,square_tests=0,proper_hits=0)
    if not h:
        result.update(status='square',factor=t,remaining=t)
        return result
    k_limit = t*j_limit//h+1
    result['raw_slots'] = slot_count(t,h,j_limit)[0]
    if dyadic_exponent is not None and n%2 == 0:
        result.update(status='trial-split',factor=2,remaining=n//2)
        return result
    if dyadic_exponent is None:
        plan = choose_wheel(n,j_limit,k_limit)
    else:
        plan = select_charts(n,j_limit,k_limit,dyadic_exponent)
    result['wheel_work'] = plan['work']
    if plan['factor'] is not None:
        f = plan['factor']
        result.update(status='trial-split',factor=f,remaining=n//f)
        return result
    charts = plan['charts'] if dyadic_exponent is not None else {'odd':plan}
    pools = []
    chart_stats = {}
    odd_masks, square_values = {}, {}
    for name, chart in charts.items():
        cut = max(0,len(chart['primes'])-drop)
        retained, deferred = list(chart['primes'][:cut]), list(chart['primes'][cut:])
        for p in retained:
            if p not in odd_masks:
                odd_masks[p] = local_directions(n,t,p,1)
        for p in deferred:
            if p not in square_values:
                square_values[p] = {d*d % p for d in range(p)}
        moduli = list(retained)
        masks = [odd_masks[p] for p in retained]
        if name != 'odd':
            directions = chart_directions(n,t,name,chart['exponent'])
            if len(directions) != chart['dyadic_labels']:
                raise ArithmeticError('dyadic mask differs from the selected chart cost')
            moduli.insert(0,2**chart['exponent'])
            masks.insert(0,directions)
        count = prod(map(len,masks))
        pools.append((name,moduli,masks,[(p,square_values[p]) for p in deferred]))
        chart_stats[name] = dict(moduli=moduli, deferred_primes=deferred, total_batches=count,
                                 full_tuples=chart['total_tuples'], started_batches=0, completed_batches=0)
    total = sum(chart['total_batches'] for chart in chart_stats.values())
    result.update(total_batches=total,unfinished_batches=total,j_limit=j_limit,k_limit=k_limit,
                  full_tuples=sum(chart['full_tuples'] for chart in chart_stats.values()))
    if dyadic_exponent is None:
        result.update(batch_primes=retained,deferred_primes=deferred,batch_modulus=prod(retained))
    else:
        result.update(charts=chart_stats,odd_only_tuples=plan['odd_only_tuples'],
                      deferred_primes={name:chart['deferred_primes'] for name,chart in chart_stats.items()},
                      setup=dict(odd_unit_images=sum(p-1 for p in odd_masks),
                                 deferred_square_images=sum(square_values),
                                 dyadic_unit_images=2**(charts['forward']['exponent']-1),
                                 dyadic_reverse_entries=charts['reverse']['dyadic_labels']))
    work = Counter()
    batches = ((name,moduli,entries,tests) for name,moduli,masks,tests in pools for entries in product(*masks))
    for name,moduli,entries,tests in batches:
        if result['started_batches'] == max_batches or result['rows']+result['point_visits'] == max_events:
            break
        result['started_batches'] += 1
        chart_stats[name]['started_batches'] += 1
        x,y = direction_basis(moduli,entries,j_limit,k_limit,work)
        result['gauss_iterations'] = work['gauss_iterations']
        for kind, value in batch_events(x,y,j_limit,k_limit,t,h,row_sieve=row_sieve,work=work):
            if result['rows']+result['point_visits'] == max_events:
                return result
            if kind == 'row':
                result['rows'] += 1
                result['rejected_rows'] += int(value)
                result['row_divisibility_tests'] = work['row_divisibility_tests']
                result['pivot_prime_tests'] = work['pivot_prime_tests']
                continue
            result['point_visits'] += 1
            j,k = value
            if gcd(j,k) != 1:
                continue
            result['primitive_points'] += 1
            delta = j*j+4*k*(t*j-h*k)
            if delta < 0:
                continue
            for p, residues in tests:
                result['deferred_checks'] += 1
                if delta%p not in residues:
                    break
            else:
                result['deferred_survivors'] += 1
                result['square_tests'] += 1
                d = isqrt(delta)
                if d*d == delta:
                    f = gcd(n,(j+2*t*k-d)//2)
                    if 1 < f < n:
                        result['proper_hits'] += 1
                        if result['factor'] is None:
                            result.update(status='split',factor=f,remaining=n//f, first_hit=[j,k])
                        if not exhaust:
                            return result
        chart_stats[name]['completed_batches'] += 1
        result['completed_batches'] += 1
        result['unfinished_batches'] -= 1
    if not result['unfinished_batches'] and result['factor'] is None:
        result['status'] = 'exhausted'
    return result


def certify(n, pair):
    with TemporaryDirectory() as temp:
        path = Path(temp)/'LatticeBatch.lean'
        path.write_text(render_certificate(n,list(pair)))
        verify_file(path)


def compare_holdout(verify=False, rounds=5):
    """Exhaust all eight published products in each mode, rotating timing order."""
    fixtures = Path(__file__).resolve().parents[1]/'research/quartic-lane-holdout.json'
    inputs = [int(row['n']) for row in json.loads(fixtures.read_text())['rows']]
    modes = ('full','one_deferred','two_deferred')
    elapsed = {name:[] for name in modes}
    totals = {}
    reference = {}
    for repeat in range(rounds):
        shift = repeat%len(modes)
        for mode in modes[shift:]+modes[:shift]:
            total = Counter()
            start = perf_counter()
            for n in inputs:
                if mode == 'full':
                    run = full_wheel_search(n,1<<18,optimize_wheel=True,exhaust=True)
                    complete = run['unchecked_tuples']==0
                else:
                    run = search(n,1<<18,drop=modes.index(mode),exhaust=True)
                    complete = run['unfinished_batches']==0
                if not complete or run['status']!='split':
                    raise ArithmeticError('incomplete holdout')
                answer = sorted((run['factor'],run['remaining'])),run['proper_hits']
                if reference.setdefault(n,answer)!=answer:
                    raise ArithmeticError('disagreement on recovered factors or number of winning positions')
                keys = ('visited_tuples','convergents','completed_batches','gauss_iterations','rows','rejected_rows',
                        'pivot_prime_tests','row_divisibility_tests','point_visits','primitive_points',
                        'deferred_checks','square_tests','proper_hits')
                total.update({key:run[key] for key in keys if key in run})
            elapsed[mode].append(perf_counter()-start)
            if totals.setdefault(mode,dict(total))!=dict(total):
                raise ArithmeticError('nondeterministic work count')
    if verify:
        for n,(pair,_) in reference.items():
            certify(n,pair)
    return dict(products=len(inputs),rounds=rounds,totals=totals,
                median_seconds={m:median(values) for m,values in elapsed.items()},primes_kernel_checked=verify)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int,nargs='?')
    parser.add_argument('--holdout',action='store_true',help='exhaust the eight fixed products in three modes')
    parser.add_argument('--max-batches',type=int, default=64)
    parser.add_argument('--max-events',type=int, default=1_000_000)
    parser.add_argument('--drop',type=int,default=1)
    parser.add_argument('--dyadic-exponent',type=int,help='select parity charts up to this exponent before batching')
    parser.add_argument('--exhaust',action='store_true')
    parser.add_argument('--no-row-sieve',action='store_true',help='disable the within-batch quadratic row test')
    parser.add_argument('--verify',action='store_true',help='certify both recovered primes in Lean')
    args = parser.parse_args()
    if args.holdout:
        if args.n is not None:
            parser.error('--holdout uses the fixed public inputs')
        print(json.dumps(compare_holdout(args.verify),indent=2))
        raise SystemExit(0)
    if args.n is None:
        parser.error('supply N or use --holdout')
    result=search(args.n,args.max_batches,drop=args.drop,max_events=args.max_events,exhaust=args.exhaust,row_sieve=not args.no_row_sieve,dyadic_exponent=args.dyadic_exponent)
    if args.verify and result['factor']:
        certify(args.n,(result['factor'],result['remaining']))
        result['primes_kernel_checked']=True
    print(json.dumps(result,indent=2))
