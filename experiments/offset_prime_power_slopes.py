"""Exact projective mask sizes and a bounded product-only odd-prime-power wheel."""

import argparse
from bisect import bisect_left
from fractions import Fraction
from itertools import product
import json
from math import gcd, isqrt, log2, prod
from pathlib import Path
from tempfile import TemporaryDirectory
from time import perf_counter

from experiments.continued_square import convergents

from experiments.offset_crt_wheel import choose_wheel, subset_products
from scripts.factor import primes_through, render_certificate, verify_file


def local_count(p, e, square):
    """Number of directions modulo p**e for odd prime p not dividing N."""
    if e < 1 or p < 3 or p % 2 == 0:
        raise ValueError('expected positive exponent and odd prime')
    power = p ** (e - 1)
    if not square:
        return (p + 1) // 2 * power
    correction = 2 * p + 1 if e % 2 else p + 2
    return ((p*p + 1) * power + 2 * correction) // (2 * (p + 1))


def local_directions(n, t, p, e):
    """Explicit normalized charts for small moduli, using only the product."""
    q = p**e
    if n % p == 0:
        raise ValueError('a prime divisor of the input requires separate handling')
    affine = {(x + n * pow(x, -1, q) - 2*t) % q for x in range(q) if x % p}
    return [(a, 1) for a in sorted(affine)] + [(1, b) for b in range(0, q, p)]


def normalized_floor(p, square):
    """Infimum of twice the number of directions divided by the modulus."""
    return Fraction(p*p + 1, p*(p+1)) if square else Fraction(p+1, p)


def all_power_lower(menu, squares, threshold, incumbent, conditioned=8):
    """Integer lower bound over all odd prime powers, including primes outside the menu.

    For the small primes distinguish omitted, exponent one, and exponent >=2.
    The last two cases can be merged where the product is a nonsquare. For r
    other prime divisors, multiply their r cheapest prices, and independently
    their r smallest normalized density floors. Unknown primes are bounded by
    the final price and by the increasing split density at the endpoint.
    """
    if conditioned < 0:
        raise ValueError('require a nonnegative conditioned prime count')
    conditioned = min(conditioned, len(menu)-1)
    small, tail = menu[:conditioned], menu[conditioned:]
    if not tail:
        raise ValueError('global certification needs a nonempty tail of known primes')
    options = []
    for p in small:
        square = squares[p]
        g = local_count(p, 1, square)
        options.append([(0, 1, Fraction(1)), (1, g, Fraction(2*g, p))]
                       + ([(1, local_count(p, 2, True), normalized_floor(p, True))]
                          if square else []))
    prices = [local_count(p, 1, squares[p]) for p in tail]
    cheapest = [1]
    while cheapest[-1] <= incumbent:
        cheapest.append(cheapest[-1] * prices[min(len(cheapest)-1, len(prices)-1)])
    rmax = len(cheapest)-1
    densities = sorted([normalized_floor(p, squares[p]) for p in tail]
                       + [normalized_floor(menu[-1], True)] * rmax)
    scale = [Fraction(1)]
    for density in densities[:rmax]:
        scale.append(scale[-1] * density/2)
    # Integer counts >= C and >= (threshold+1)*scale coexist. With r
    # increasing the first bound grows and the second decreases.
    crossings = [Fraction(c, 1) / s for c, s in zip(cheapest, scale)]
    lower, states = incumbent, 0
    for case in product(*options):
        states += 1
        base = prod(c for _, c, _ in case)
        size = sum(r for r, _, _ in case)
        multiplier = prod(a for _, _, a in case) * Fraction(threshold+1, 2**size)
        cut = bisect_left(crossings, multiplier/base)
        for r in {max(0, cut-1), min(rmax, cut)}:
            x = multiplier * scale[r]
            lower = min(lower, max(base*cheapest[r], -(-x.numerator//x.denominator)))
    return dict(lower=lower, conditioned=len(small), states=states, tail_cardinalities=rmax+1)


def choose_powers(n, j, k, *, lift=(3, 5, 7), max_exponent=4, conditioned=8, extra_free=6):
    """Minimize over 0..max_exponent on lift and 0..1 on the old free menu.

    An evenly spaced subset of the old fixed primes can also vary. Trial division and character tests use
    the same public menu as the distinct-prime plan.
    """
    base = choose_wheel(n, j, k)
    if base['factor'] is not None:
        return dict(factor=base['factor'])
    menu = tuple(sorted(base['fixed'] + base['free']))
    signs = {p: pow(n % p, (p-1)//2, p)==1 for p in menu}
    if extra_free < 0:
        raise ValueError('require nonnegative extra free primes')
    old_fixed = base['fixed']
    count = min(extra_free, len(old_fixed))
    moved = {old_fixed[i*(len(old_fixed)-1)//max(count-1, 1)] for i in range(count)}
    fixed = tuple(p for p in old_fixed if p not in moved)
    available = tuple(sorted(set(base['free']) | moved))
    lift = tuple(p for p in lift if p in available)
    if max_exponent < 1 or len(lift)!=len(set(lift)):
        raise ValueError('require a positive exponent limit and distinct lifted primes')
    free = tuple(p for p in available if p not in lift)
    fixed_m = prod(fixed)
    prices = {p: local_count(p, 1, signs[p]) for p in menu}
    fixed_g = prod(prices[p] for p in fixed)
    # Every right prefix threshold can be answered with a single bisection.
    # Give the lifted states to the left to balance the table sizes.
    lift_options = [[(1, 1, 0)] + [(p**e, local_count(p, e, signs[p]), e)
                                  for e in range(1, max_exponent+1)] for p in lift]
    split = max(0, (len(free) - (prod(map(len, lift_options))-1).bit_length()) // 2)
    left_p, right_p = free[:split], free[split:]
    left = subset_products(left_p, prices)
    right = sorted(subset_products(right_p, prices))
    suffix = [None]*len(right)
    best = None
    for i in reversed(range(len(right))):
        m, g, mask = right[i]
        best = min((g, m, mask), best) if best else (g, m, mask)
        suffix[i] = best
    right_m = [v[0] for v in right]
    winner = None
    checks = 0
    for opts in product(*lift_options):
        start_g = fixed_g * prod(g for _, g, _ in opts)
        start_m = fixed_m * prod(m for m, _, _ in opts)
        exps = tuple(e for _, _, e in opts)
        for lm, lg, lmask in left:
            checks += 1
            index = bisect_left(right_m, base['threshold']//(start_m*lm)+1)
            if index == len(right):
                continue
            rg, rm, rmask = suffix[index]
            item = (start_g*lg*rg, start_m*lm*rm, exps, lmask, rmask)
            if winner is None or item < winner:
                winner = item
    g, m, exps, lmask, rmask = winner
    selected = dict.fromkeys(fixed, 1)
    selected.update((p,e) for p,e in zip(lift,exps) if e)
    selected.update((p,1) for values,mask in [(left_p,lmask),(right_p,rmask)]
                    for i,p in enumerate(values) if mask & (1<<i))
    assert m == prod(p**e for p,e in selected.items()) > base['threshold']
    assert g == prod(local_count(p,e,signs[p]) for p,e in selected.items()) <= base['total_tuples']
    return dict(factor=None, powers=sorted(selected.items()), count=g, modulus=m,
                distinct_count=base['total_tuples'], queries=checks, right_subsets=len(right),
                selection_work=dict(distinct_wheel=base['work'], repeated_character_tests=len(menu),
                                    mixed_left_subsets=len(left), mixed_right_subsets=len(right),
                                    lifted_states=prod(map(len,lift_options)), mixed_queries=checks),
                global_bound=all_power_lower(menu,signs,base['threshold'],g,conditioned))


def normalized_line(moduli, directions, *, k_limit=None):
    """Return I,m,A so the complete lattice is k=I*v, j=A*v modulo m."""
    if len(moduli) != len(directions):
        raise ValueError('each modulus requires one direction')
    divisors = [gcd(b,q) for (_,b),q in zip(directions,moduli)]
    common = prod(divisors)
    if k_limit is not None and common > k_limit:
        return None
    residue, modulus = 0, 1
    for (a,b),q,d in zip(directions,moduli,divisors):
        reduced = q//d
        if reduced == 1:
            continue
        target = a*(common//d)*pow(b//d, -1, reduced) % reduced
        residue += modulus*((target-residue)*pow(modulus,-1,reduced) % reduced)
        modulus *= reduced
    return common, modulus, residue


def reconstruct(moduli, directions, j_limit, k_limit):
    """Recover the unique primitive point via the reduced approximant w/v."""
    line = normalized_line(moduli, directions, k_limit=k_limit)
    if line is None:
        return None
    common, modulus, residue = line
    for w,v in convergents(residue,modulus):
        k = v*common
        if k > k_limit:
            break
        j = v*residue-w*modulus
        if 1 <= j <= j_limit and gcd(j,k)==1:
            return j,k
    return None


def enumerate_plan(n, j, k, plan, budget, *, exhaust=True):
    """Run a complete or bounded wheel on public inputs; keep every proper hit."""
    total = plan['count']
    t = isqrt(n)
    h = n-t*t
    moduli = [p**e for p,e in plan['powers']]
    if not 2*j*k < prod(moduli) or budget < 0:
        raise ValueError('positive enclosing box must satisfy strict reconstruction bound')
    allowed = [local_directions(n,t,p,e) for p,e in plan['powers']]
    if total != prod(map(len,allowed)):
        raise ArithmeticError('enumerated direction counts disagree with exact formula')
    visited, tests, hits = 0, 0, []
    for dirs in product(*allowed):
        if visited == budget:
            break
        visited += 1
        point = reconstruct(moduli,dirs,j,k)
        if point is None:
            continue
        offset,multiplier = point
        if multiplier > t*offset//h+1:
            continue
        delta = offset**2+4*multiplier*(t*offset-h*multiplier)
        if delta < 0:
            continue
        tests += 1
        root = isqrt(delta)
        if root*root == delta:
            factor = gcd(n,(offset+2*t*multiplier-root)//2)
            if 1 < factor < n:
                hits.append((offset,multiplier,factor))
                if not exhaust:
                    break
    return dict(visited=visited,unchecked=total-visited,square_tests=tests,hits=hits,
                chart_inverses=sum((p-1)*p**(e-1) for p,e in plan['powers']),
                chart_directions=sum(map(len,allowed)))


def search(n, max_tuples, *, exhaust=False, conditioned=8):
    """Choose the odd powers and run the bounded public schedule on a nonsquare product."""
    if not 4 <= n < 2**2048 or max_tuples < 0:
        raise ValueError('expected a positive budget or zero and 4 <= N < 2^2048')
    t = isqrt(n)
    h = n-t*t
    if h == 0:
        return dict(status='split',factor=t,remaining=t,visited=0,unchecked=0,total_tuples=0)
    j = isqrt(4*h//3)
    k = t*j//h+1
    plan = choose_powers(n,j,k,conditioned=conditioned)
    if plan['factor'] is not None:
        f = plan['factor']
        return dict(status='split',factor=f,remaining=n//f,visited=0,unchecked=0,total_tuples=0)
    result = enumerate_plan(n,j,k,plan,max_tuples,exhaust=exhaust)
    factor = result['hits'][0][2] if result['hits'] else None
    return dict(**result, status='split' if factor else ('partial' if result['unchecked'] else 'exhausted'),
                factor=factor, remaining=n//factor if factor else n, powers=plan['powers'],
                total_tuples=plan['count'], distinct_count=plan['distinct_count'], modulus=plan['modulus'],
                selection_queries=plan['queries'], right_subsets=plan['right_subsets'],
                selection_work=plan['selection_work'], bound_states=plan['global_bound']['states'],
                all_powers_lower=plan['global_bound']['lower'])


def holdout(verify):
    """Compare full wheels on the eight existing public products. Never read factor labels."""
    from experiments.offset_crt_reconstruction import search
    rows = json.loads((Path(__file__).resolve().parents[1]/'research/quartic-lane-holdout.json').read_text())['rows']
    with TemporaryDirectory() as temp:
        for row in rows:
            n = int(row['n'])
            t = isqrt(n)
            h = n-t*t
            j = isqrt(4*h//3)
            k = t*j//h+1
            start = perf_counter()
            old = search(n,1<<18,exhaust=True,optimize_wheel=True)
            old_time = perf_counter()-start
            start = perf_counter()
            plan = choose_powers(n,j,k)
            new = enumerate_plan(n,j,k,plan,1<<18)
            new_time = perf_counter()-start
            assert old['unchecked_tuples'] == new['unchecked'] == 0
            assert len(new['hits']) == old['proper_hits'] > 0
            assert all(f in (old['factor'],old['remaining']) for _,_,f in new['hits'])
            factor = new['hits'][0][2]
            factors = sorted([factor,n//factor])
            if verify:
                certificate = Path(temp)/'PrimePowerControl.lean'
                certificate.write_text(render_certificate(n,factors))
                verify_file(certificate)
            yield dict(sample=row['sample'], n=str(n), factors=factors, checked=verify,
                       distinct=old['visited_tuples'], mixed=new['visited'],
                       distinct_tests=old['square_tests'], mixed_tests=new['square_tests'],
                       seconds=[round(old_time,4),round(new_time,4)],hits=len(new['hits']),
                       lifts=[v for v in plan['powers'] if v[1]>1])


def verify_charts():
    checked = 0
    for p in primes_through(11)[1:]:
        for e in range(1,5):
            q = p**e
            if q > 800:
                continue
            squares = {x*x % q for x in range(q)}
            for n in range(1,2*p+1):
                if n%p == 0:
                    continue
                t = isqrt(n)
                actual = set(local_directions(n,t,p,e))
                expected = {(a,b) for a,b in ([(a,1) for a in range(q)]
                                             + [(1,b) for b in range(0,q,p)])
                            if ((a+2*t*b)**2-4*n*b*b)%q in squares}
                assert actual == expected
                assert len(actual) == local_count(p,e,pow(n,(p-1)//2,p)==1)
                checked += 1
    return checked


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--conditioned', type=int, default=8)
    parser.add_argument('--max-tuples', type=int, default=64)
    parser.add_argument('n', nargs='?', type=int)
    parser.add_argument('--holdout', action='store_true')
    parser.add_argument('--verify', action='store_true', help='kernel-check each holdout split')
    args = parser.parse_args()
    if args.holdout:
        for record in holdout(args.verify):
            print(json.dumps(record), flush=True)
        raise SystemExit
    if args.n is not None:
        report = search(args.n, args.max_tuples, conditioned=args.conditioned)
        if args.verify and report['factor'] is not None:
            with TemporaryDirectory() as temporary:
                certificate = Path(temporary)/'PrimePowerSplit.lean'
                certificate.write_text(render_certificate(args.n,sorted((report['factor'],report['remaining']))))
                verify_file(certificate)
            report['prime_split_checked'] = True
        print(json.dumps(report))
        raise SystemExit
    if args.verify:
        parser.error('--verify requires --holdout or an explicit integer')
    print('checked charts:', verify_charts())
    rows = json.loads((Path(__file__).resolve().parents[1]/'benchmarks/offset-crt.json').read_text())
    for row in rows:
        if row['id'] not in ('offset-crt-mixed-134683853','offset-crt-fresh-2048','offset-crt-crossed-2048'):
            continue
        start = perf_counter()
        report = search(int(row['n']),args.max_tuples,conditioned=args.conditioned)
        print(row['id'], 'distinct, mixed, all-power floor (bits):',
              [round(log2(report[key]),7) for key in ('distinct_count','total_tuples','all_powers_lower')],
              'lifts:', [(p,e) for p,e in report['powers'] if e>1],
              'total:', report['total_tuples'], 'unchecked:', report['unchecked'],
              'visited:', report['visited'], 'square tests:', report['square_tests'],
              'status:',report['status'],'queries:', report['selection_queries'],
              'seconds:',round(perf_counter()-start,4))
