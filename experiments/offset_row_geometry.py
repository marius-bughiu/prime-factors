"""Group primitive offset candidates by the forced next digit at singular odd slopes."""

import argparse
from collections import Counter
from functools import cache
from itertools import product
import json
from math import gcd, isqrt, prod
from pathlib import Path
from statistics import median
from time import perf_counter

from experiments.complete_offset_search import slot_count
from experiments.offset_crt_wheel import choose_wheel
from experiments.offset_lattice_batches import batch_events, certify, direction_basis, search as ordinary_search
from experiments.offset_prime_power_slopes import local_directions


def lifted_directions(n, t, p, work):
    """Return (modulus, j entry, k entry) for each allowed direction at p."""
    q = p*p
    shift = 2*t % q
    product_term = 4*n % q
    entries = []
    for a, b in local_directions(n, t, p, 1):
        if b:
            value = (a + shift)**2 - product_term
            work['singular_tests'] += 1
            if value % p == 0:
                digit = -(value//p) * pow(2*(a+shift), -1, p) % p
                lifted = a + p*digit
                assert ((lifted+shift)**2-product_term) % q == 0
                entries.append((q, lifted, b))
                work['newton_digits'] += 1
                continue
        entries.append((p, a, b))
    work['unit_images'] += p-1
    return entries


def schedule(retained, masks, reserve_size, work):
    """Choose the cheapest reserve-prime query at each remaining index requirement."""
    sizes = {p: len(masks[p]) for p in retained}
    singular = {p: sum(m != p for m, _, _ in masks[p]) for p in retained}
    reserve = tuple(retained[:reserve_size])
    prefix = retained[len(reserve):]
    target = prod(reserve)

    @cache
    def best(available, need):
        work['reserve_states'] += 1
        if need == 1:
            return 1, None
        choices = []
        for p in available:
            rest = tuple(q for q in available if q != p)
            regular_cost = best(rest, -(-need//p))[0]
            total = (sizes[p]-singular[p])*regular_cost
            if singular[p]:
                total += singular[p]*best(rest, -(-need//(p*p)))[0]
            choices.append((total, p))
            work['reserve_queries'] += 1
        return min(choices)

    # The current need is ceil(target / product of all forced extra primes).
    # Each state represents exactly its counted number of distinct prefix classes.
    counts = Counter({target: 1})
    for p in prefix:
        following = Counter()
        for need, multiplicity in counts.items():
            following[need] += (sizes[p]-singular[p])*multiplicity
            if singular[p]:
                following[-(-need//p)] += singular[p]*multiplicity
            work['prefix_count_states'] += 1
        counts = following
    leaves = sum(multiplicity*best(reserve,need)[0] for need,multiplicity in counts.items())

    def grow(available, need, selected):
        _, p = best(available, need)
        if p is None:
            yield selected, available
            return
        work['reserve_nodes_opened'] += 1
        rest = tuple(q for q in available if q != p)
        for entry in masks[p]:
            yield from grow(rest, -(-need//entry[0]), (*selected, entry))

    def batches():
        for labels in product(*(masks[p] for p in prefix)):
            work['prefix_tuples_opened'] += 1
            gain = prod(m//p for p,(m,_,_) in zip(prefix,labels))
            yield from grow(reserve, -(-target//gain), labels)

    return leaves, batches, reserve


def search(n, max_batches, *, drop=1, reserve_size=4, max_events=1_000_000, exhaust=False, primitive_rows=False):
    """Use the same odd wheel and minimum batch determinant as the ordinary lattice search."""
    if not 4 <= n < 2**2048 or min(max_batches,max_events,drop,reserve_size) < 0 or reserve_size > 8:
        raise ValueError('expected 4 <= N < 2^2048, nonnegative budgets and reserve size <= 8')
    t = isqrt(n)
    h = n-t*t
    work = Counter()
    report = dict(status='partial', factor=None, remaining=n, first_hit=None, proper_hits=0,
                  raw_slots=0, square_tests=0, rows=0, rejected_rows=0, point_visits=0,
                  primitive_points=0, baseline_batches=0, total_batches=0, unfinished_batches=0,
                  started_batches=0, completed_batches=0, deferred_checks=0, second_digit_checks=0,
                  max_batches=max_batches, max_events=max_events, drop=drop, reserve_size=reserve_size,
                  work=work)
    if h == 0:
        report.update(status='square',factor=t,remaining=t)
        return report
    j_limit = isqrt(4*h//3)
    k_limit = t*j_limit//h+1
    report['raw_slots'] = slot_count(t,h,j_limit)[0]
    selected = choose_wheel(n,j_limit,k_limit)
    report['wheel_work'] = selected['work']
    if selected['factor'] is not None:
        f = selected['factor']
        report.update(status='trial-split',factor=f,remaining=n//f)
        return report
    wheel = selected['primes']
    cut = max(0, len(wheel)-drop)
    retained, deferred = wheel[:cut],wheel[cut:]
    masks = {p:lifted_directions(n,t,p,work) for p in retained}
    total, enumerate_batches, reserve = schedule(retained,masks,reserve_size,work)
    # No quadratic tuple table is needed at a deferred prime. A separate zero
    # residue test distinguishes points whose square would have odd valuation.
    square_sets = {p:{i*i % p for i in range(p)} for p in (*deferred,*reserve)}
    work['deferred_square_images'] = sum(square_sets)
    baseline = prod(len(mask) for mask in masks.values())
    minimum = prod(retained)
    report.update(baseline_batches=baseline,total_batches=total,unfinished_batches=total,
                  full_tuples=selected['total_tuples'],minimum_modulus=minimum,
                  retained_primes=list(retained), reserve_primes=list(reserve))
    groups = enumerate_batches()
    while report['started_batches'] < min(max_batches,total) and report['rows']+report['point_visits'] < max_events:
        entries, unused = next(groups)
        moduli = [m for m,_,_ in entries]
        assert prod(moduli) >= minimum
        directions = [(a,b) for _,a,b in entries]
        x,y = direction_basis(moduli,directions,j_limit,k_limit,work)
        report['started_batches'] += 1
        tests = [(p,square_sets[p]) for p in (*unused,*deferred)]
        for kind,value in batch_events(x,y,j_limit,k_limit,t,h,row_sieve=True,work=work,primitive_rows=primitive_rows):
            if report['rows']+report['point_visits'] == max_events:
                return report
            if kind == 'row':
                report['rows'] += 1
                report['rejected_rows'] += int(value)
                continue
            report['point_visits'] += 1
            j,k = value
            if gcd(j,k) != 1:
                continue
            report['primitive_points'] += 1
            delta = j*j+4*k*(t*j-h*k)
            if delta < 0:
                continue
            for p,residues in tests:
                report['deferred_checks'] += 1
                r = delta % p
                if r not in residues:
                    break
                if r == 0:
                    report['second_digit_checks'] += 1
                    if delta % (p*p):
                        break
            else:
                report['square_tests'] += 1
                d = isqrt(delta)
                if d*d == delta:
                    factor = gcd(n, (j+2*t*k-d)//2)
                    if 1 < factor < n:
                        report['proper_hits'] += 1
                        if report['factor'] is None:
                            report.update(status='split',factor=factor,remaining=n//factor,first_hit=[j,k])
                        if not exhaust:
                            return report
        report['completed_batches'] += 1
        report['unfinished_batches'] -= 1
    if report['unfinished_batches'] == 0 and report['factor'] is None:
        report['status'] = 'exhausted'
    return report


def compare_holdout(verify=False, rounds=5):
    """Exhaust all eight products in each mode, rotating order for search-only medians."""
    fixture = Path(__file__).resolve().parents[1]/'research/quartic-lane-holdout.json'
    inputs = [int(row['n']) for row in json.loads(fixture.read_text())['rows']]
    modes = ('ordinary', 'lift_only', 'four_reserves')
    timings = {mode:[] for mode in modes}
    results = {}
    for index in range(rounds):
        shift = index % len(modes)
        for mode in modes[shift:] + modes[:shift]:
            totals = Counter()
            pairs = []
            start = perf_counter()
            for n in inputs:
                opts = dict(drop=2, exhaust=True)
                if mode == 'ordinary':
                    run = ordinary_search(n, 65536, **opts)
                    totals['gauss_iterations'] += run['gauss_iterations']
                else:
                    run = search(n, 65536, reserve_size=0 if mode=='lift_only' else 4, **opts)
                    totals.update(run['work'])
                if run['unfinished_batches'] or run['factor'] is None:
                    raise ArithmeticError('holdout search did not complete with a split')
                pairs.append(sorted((run['factor'],run['remaining'])))
                for key in ('total_batches','rows','point_visits','square_tests','proper_hits','deferred_checks'):
                    totals[key] += run[key]
            timings[mode].append(perf_counter()-start)
            results[mode] = dict(totals,pairs=pairs)
    for mode in modes:
        if results[mode]['pairs'] != results['ordinary']['pairs']:
            raise ArithmeticError('holdout modes disagree on factor pairs')
        results[mode]['median_search_seconds'] = median(timings[mode])
    if verify:
        for n, pair in zip(inputs,results['four_reserves']['pairs']):
            certify(n, pair)
    return dict(runs=results, rounds=rounds, checked_certificates=len(inputs) if verify else 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int,nargs='?')
    parser.add_argument('--holdout',action='store_true',help='compare all modes on eight fixed products')
    parser.add_argument('--max-batches',type=int,default=8)
    parser.add_argument('--max-events',type=int,default=1_000_000)
    parser.add_argument('--drop',type=int,default=1)
    parser.add_argument('--reserve-size',type=int,default=4)
    parser.add_argument('--exhaust',action='store_true')
    parser.add_argument('--primitive-rows',action='store_true',help='also apply the primitive-axis determinant and valuation checks')
    parser.add_argument('--verify',action='store_true')
    opts = vars(parser.parse_args())
    verify = opts.pop('verify')
    if opts.pop('holdout'):
        print(json.dumps(compare_holdout(verify=verify),indent=2))
        return
    if opts['n'] is None:
        parser.error('provide N or --holdout')
    result = search(**opts)
    if verify and result['factor'] is not None:
        certify(opts['n'],(result['factor'],result['remaining']))
        result['primes_kernel_checked'] = True
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
