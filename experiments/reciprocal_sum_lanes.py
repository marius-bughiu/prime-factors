"""Price complementary wheel lanes and discard a whole lower progression with no possible factor sum."""

import argparse
import json
from math import gcd, isqrt
from pathlib import Path
from time import process_time_ns

from .affine_radix_holdout import draw_prime
from .reciprocal_wheel import band, ordinary, search as grouped_rectangle, wheel_roots

ROOT = Path(__file__).resolve().parents[1]
SEED = b'reciprocal-sum-lanes-v1'
SIDES = (19, 20, 21, 19, 20, 21, 19, 20)
SQUARE_MODULI = (64, 11, 13, 17, 19, 23)
METHODS = ('wide_rectangle', 'tight_rectangle', 'sum', 'guarded_sum')


def progression(low, high, wheel, residue):
    """All integers congruent to residue in the closed interval."""
    return range(low+(residue-low) % wheel, high+1, wheel)


def schedule(n, wheel, width, max_blocks, from_end):
    if n < 3 or n % 2 == 0 or wheel < 1 or width < 1 or max_blocks < 0:
        raise ValueError('expected odd N>=3, a positive wheel and width, and a nonnegative cap')
    low, high = band(n)
    total = (high-low+width)//width
    count = min(max_blocks, total)
    first = total-count if from_end else 0
    return low, high, total, first, count


def search(n, wheel, width, max_blocks, *, from_end=False, method='sum'):
    """Multiply lower candidates surviving the exact lane test, at most max_blocks blocks."""
    if method not in METHODS:
        raise ValueError(f'unknown method {method}')
    low, high, total, first, count = schedule(n, wheel, width, max_blocks, from_end)
    common = gcd(wheel, n)
    if common != 1:
        raise ValueError('the reciprocal permutation requires a wheel coprime to N')
    residues = wheel_roots(n, wheel)
    work = dict(wheel_gcds=1+wheel, wheel_inverses=len(residues), blocks=count,
                residue_lanes=0, lane_pricings=0, endpoint_quotients=0, guarded_blocks=0,
                guard_tests=0, empty_lanes=0, ordinary_lower_terms=0, lower_terms_omitted=0,
                product_terms=0, final_gcds=1)
    product = 1
    for j in range(first, first+count):
        left, right = low+j*width, min(low+(j+1)*width-1, high)
        guarded = False
        if method == 'guarded_sum':
            work['guard_tests'] += 1
            m = (right-left+1)//wheel-1
            guarded = m >= 1 and m*(n-right*right) >= right*right
            work['guarded_blocks'] += guarded
        if method == 'wide_rectangle':
            lower_q, upper_q = (n+right-1)//right, n//left
            work['endpoint_quotients'] += 2
        for r, s in residues:
            lower = progression(left, right, wheel, r)
            if not lower:
                continue
            work['residue_lanes'] += 1
            work['ordinary_lower_terms'] += len(lower)
            chosen = lower
            if not guarded:
                work['lane_pricings'] += 1
                if method != 'wide_rectangle':
                    a, b = lower[0], lower[-1]
                    lower_q, upper_q = (n+b-1)//b, n//a
                    work['endpoint_quotients'] += 2
                partner = progression(lower_q, upper_q, wheel, s)
                if method in ('sum', 'guarded_sum'):
                    # The number of feasible sums is len(partner) - (len(lower)-1).
                    if len(partner) < len(lower):
                        work['empty_lanes'] += 1
                        work['lower_terms_omitted'] += len(lower)
                        continue
                elif len(partner) < len(lower):
                    chosen = partner
            work['product_terms'] += len(chosen)
            for x in chosen:
                product = (product*x) % n
    found = gcd(product, n)
    return dict(factor=found if 1 < found < n else None, product=str(product), gcd=str(found),
                blocks_needed=str(total), first_block=str(first), untested_blocks=str(total-count),
                complete=count == total, work=work)


def fermat(n, wheel, width, max_blocks, *, from_end=False, exhaust=False):
    """Search increasing admissible sums with a wheel and six local square screens."""
    low, high, total, first, count = schedule(n, wheel, width, max_blocks, from_end)
    if gcd(n, wheel) != 1:
        raise ValueError('expected a wheel coprime to N')
    pairs = wheel_roots(n, wheel)
    residues = sorted({(r+s) % wheel for r, s in pairs})
    masks = [{(i*i) % m for i in range(m)} for m in SQUARE_MODULI]
    work = dict(wheel_gcds=1+wheel, wheel_inverses=len(pairs),
                square_residues_built=sum(SQUARE_MODULI), wheel_sum_residues=len(residues),
                sum_candidates=0, screen_reductions=0, square_tests=0, endpoint_quotients=0)
    if not count:
        return dict(factor=None, work=work)
    start, end = low+first*width, min(high, low+(first+count)*width-1)
    sum_lo, sum_hi = end+(n+end-1)//end, start+n//start
    work['endpoint_quotients'] = 2
    factor = None
    for cycle in range(sum_lo//wheel, sum_hi//wheel+1):
        for residue in residues:
            z = cycle*wheel+residue
            if z < sum_lo or z > sum_hi:
                continue
            work['sum_candidates'] += 1
            delta = z*z-4*n
            if delta < 0:
                continue
            for m, mask in zip(SQUARE_MODULI, masks):
                work['screen_reductions'] += 1
                if delta % m not in mask:
                    break
            else:
                work['square_tests'] += 1
                root = isqrt(delta)
                if root*root == delta and (z-root) % 2 == 0:
                    p = (z-root)//2
                    if start <= p <= end and 1 < p < n and n % p == 0:
                        factor = p
                        if not exhaust:
                            return dict(factor=factor, work=work)
    return dict(factor=factor, work=work)


def sample():
    attempt = 0
    seen = set()
    for bits in SIDES:
        while True:
            index = attempt
            attempt += 1
            p, q = sorted(draw_prime(side, index, bits=bits, seed=SEED) for side in (b'p', b'q'))
            n = p*q
            if n.bit_length() == 2*bits and p < q and n not in seen and gcd(n, 210) == 1:
                seen.add(n)
                yield index, n, [p, q]
                break


def timed(call):
    start = process_time_ns()
    result = call()
    return result, (process_time_ns()-start)/1e9


def panel(verify=False):
    from scripts.factor import render_certificate, verify_file
    records = []
    for i, (draw, n, labels) in enumerate(sample()):
        row = dict(n=str(n), draw=draw, factors=[str(p) for p in labels], methods={})
        cap = 4096
        methods = list(METHODS) + ['fermat', 'ordinary_batched', 'narrow_rectangle']
        for name in methods[i % len(methods):]+methods[:i % len(methods)]:
            if name in METHODS:
                out, cpu = timed(lambda: search(n, 210, 840, cap, method=name))
                if not out['complete']:
                    raise ValueError('incomplete small input')
            elif name == 'fermat':
                out, cpu = timed(lambda: fermat(n, 210, 840, cap))
            elif name == 'ordinary_batched':
                out, cpu = timed(lambda: ordinary(n, 210))
            else:
                lo, hi = band(n)
                out, cpu = timed(lambda: grouped_rectangle(n, 210, 28, (hi-lo)//28+1))
            f = out['factor']
            if f is not None and f not in labels:
                raise ValueError('invalid factor')
            if name in ('sum', 'guarded_sum', 'fermat', 'ordinary_batched', 'narrow_rectangle') and f != labels[0]:
                raise ValueError(f'{name} missed a complete case')
            row['methods'][name] = dict(out, cpu_seconds=round(cpu, 6))
        if verify:
            path = ROOT/'build'/'reciprocal-sum-lane-proofs'/f'sample-{i}.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            f = row['methods']['sum']['factor']
            path.write_text(render_certificate(n, [f, n//f]))
            verify_file(path)
        full, secs = timed(lambda: fermat(n, 210, 840, cap, exhaust=True))
        if full['factor'] != labels[0]:
            raise ValueError('complete Fermat comparison disagreed')
        row['methods']['fermat_complete'] = dict(full, cpu_seconds=round(secs, 6))
        records.append(row)
    controls = []
    for source in json.loads((ROOT/'benchmarks'/'near-smooth-sum.json').read_text())[-2:]:
        n = int(source['n'])
        for tail in (False, True):
            results = {}
            for name in METHODS:
                out = search(n, 210, 840, 2, from_end=tail, method=name)
                results[name] = out
            results['fermat'] = fermat(n, 210, 840, 2, from_end=tail)
            controls.append(dict(input=source['id'], n=str(n), end='last' if tail else 'first',
                                 remaining=[] if results['sum']['factor'] else [str(n)], methods=results))
    return compact_panel(records, controls, verify)


def compact_panel(records, controls, verify):
    summary = {}
    for name in records[0]['methods']:
        runs = [row['methods'][name] for row in records]
        counts = runs[0].get('work', runs[0])
        keys = [k for k, value in counts.items() if type(value) is int and k != 'factor']
        totals = {k: sum(run.get('work', run)[k] for run in runs) for k in keys}
        summary[name] = dict(work=totals, splits=sum(run['factor'] is not None for run in runs),
                             cpu_seconds=round(sum(run['cpu_seconds'] for run in runs), 6))
    compact = []
    for row in records:
        routes = {}
        for name, run in row['methods'].items():
            if name in METHODS:
                routes[name] = dict(gcd=run['gcd'], terms=run['work']['product_terms'],
                                    pricings=run['work']['lane_pricings'], cpu_seconds=run['cpu_seconds'])
            else:
                routes[name] = {k: v for k, v in run.items()
                                if k not in ('product', 'blocks_needed', 'complete', 'first_block')}
        compact.append(dict(n=row['n'], draw=row['draw'], factors=row['factors'], methods=routes))
    compact_controls = []
    for row in controls:
        ref = row['methods']['sum']
        n = int(row['n'])
        lo, hi = band(n)
        start = lo+int(ref['first_block'])*840
        end = min(start+2*840-1, hi)
        compact_controls.append(dict(input=row['input'], end=row['end'], n=row['n'], remaining=row['remaining'],
                                     first=str(start), last=str(end), positions=end-start+1,
                                     blocks_needed=ref['blocks_needed'], untested_blocks=ref['untested_blocks'],
                                     sum_lower=str(end+(n+end-1)//end), sum_upper=str(start+n//start),
                                     methods={name: {k: run[k] for k in ('gcd', 'work', 'factor') if k in run}
                                              for name, run in row['methods'].items()}))
    return dict(seed=SEED.decode(), side_bits=SIDES, wheel=210, width=840, square_moduli=SQUARE_MODULI,
                small_max_blocks=4096, fullsize_blocks_per_end=2, lean_verified_small_pairs=8 if verify else 0,
                timings='One process-CPU observation per method and input. Primary method order rotates. '
                        'Complete Fermat was added after the primary comparison.',
                summary=summary, cases=compact, control_sections=compact_controls)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?')
    parser.add_argument('--wheel', type=int, default=210)
    parser.add_argument('--width', type=int, default=840)
    parser.add_argument('--max-blocks', type=int, default=2)
    parser.add_argument('--from-end', action='store_true')
    parser.add_argument('--method', choices=METHODS, default='sum')
    parser.add_argument('--panel', action='store_true')
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    if args.panel:
        print(json.dumps(panel(args.verify), indent=2))
    elif args.n is not None:
        print(json.dumps(search(args.n, args.wheel, args.width, args.max_blocks,
                                from_end=args.from_end, method=args.method), indent=2))
    else:
        parser.error('supply N or --panel')
