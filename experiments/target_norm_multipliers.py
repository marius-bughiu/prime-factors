"""Skip multipliers that cannot represent a chosen square class as a convergent norm."""

import argparse
import json
from math import gcd, isqrt, prod
from pathlib import Path
from statistics import median
from time import process_time_ns

from experiments.mixed_ratio_heights import jacobi
from experiments.pell_pairs import convergents
from scripts.factor import primes_through


ROOT = Path(__file__).resolve().parents[1]
SMALL_PRIMES = (2, 3, 5, 7, 11)


def target(n):
    # Products of two distinct odd primes outside SMALL_PRIMES are assumed.
    if gcd(n, prod(SMALL_PRIMES)) != 1:
        raise ValueError('expected an input coprime to the small support')
    values = sorted(prod(p for i, p in enumerate(SMALL_PRIMES) if mask >> i & 1)
                    for mask in range(1, 1 << len(SMALL_PRIMES)))
    return next(d for d in values if jacobi(d, n) == 1)


def primitive_mod16(d):
    scaled_squares = {d*a*a % 16 for a in range(8)}
    return {b for b in range(16) if any((x*x-b*y*y) % 16 in scaled_squares
                                        for x in range(8) for y in range(8) if x % 2 or y % 2)}


def scan(n, limit, steps, filtered, *, audit_gcds=False):
    if n < 3 or isqrt(n)**2 == n or limit < 1 or steps < 1:
        raise ValueError('expected a nonsquare product and positive budgets')
    d = target(n)
    primes = primes_through(limit)
    d_odd_primes = [p for p in SMALL_PRIMES if p > 2 and d % p == 0]
    allowed_2adic = primitive_mod16(d) if filtered else None
    eligible = skipped = visits = 0
    factor = first_root = incidental = None
    for k in range(1, limit+1):
        shared = gcd(k, n)
        if 1 < shared < n:
            factor = dict(value=str(shared), multiplier=k, source='multiplier gcd')
            break
        factors = [p for p in primes if k % p == 0]
        if prod(factors) != k or gcd(k, n*d) != 1:
            continue
        eligible += 1
        if filtered and (k*n % 16 not in allowed_2adic or
                         any(jacobi(d, p) != 1 for p in factors if p > 2) or
                         any(jacobi(k*n, p) != 1 for p in d_odd_primes)):
            skipped += 1
            continue
        for i, norm, sign, numerator, center in convergents(n, k, steps):
            visits += 1
            if audit_gcds and incidental is None:
                common = gcd(norm, n)
                if 1 < common < n:
                    incidental = dict(value=str(common), multiplier=k, step=i)
            if sign > 0 and norm % d == 0:
                scale = isqrt(norm//d)
                if d*scale*scale == norm:
                    common = gcd(scale, n)
                    if 1 < common < n:
                        factor = dict(value=str(common), multiplier=k, step=i, source='scale gcd')
                        break
                    if common == 1:
                        root = numerator*pow(scale, -1, n) % n
                        if (root*root-d) % n:
                            raise ArithmeticError('incorrect square-root witness')
                        witness = dict(root=str(root), multiplier=k, step=i, visits=visits)
                        if first_root is None:
                            first_root = witness
                        else:
                            common = gcd(root-int(first_root['root']), n)
                            if 1 < common < n:
                                factor = dict(value=str(common), source='different roots', **witness)
                                break
            if center or norm == 1:
                break
        if factor:
            break
    return dict(target=d, eligible_multipliers=eligible, skipped_multipliers=skipped, steps=visits,
                first_root=first_root, target_factor=factor, **({'incidental_factor': incidental} if audit_gcds else {}))


def report():
    source = json.loads((ROOT/'research/projected-divisor-wheel.json').read_text())
    cases = [(r['n'], r['panel'], r['bits']) for r in source['rows']]
    expected = {r['n']: r['factorization'] for r in source['rows']}
    controls = json.loads((ROOT/'benchmarks/projected-divisor-wheel.json').read_text())
    cases += [(c['n'], c['id'], 1024) for c in controls if c['status'] == 'partial']
    rows = []
    for sample, (decimal, panel, bits) in enumerate(cases):
        n = int(decimal)
        timings = {m: [] for m in ('all', 'filtered')}
        results = {}
        for repeat in range(4):
            order = ('all', 'filtered') if (repeat+sample) % 2 == 0 else ('filtered', 'all')
            for method in order:
                start = process_time_ns()
                work = scan(n, 320, 256, method == 'filtered')
                timings[method].append(process_time_ns()-start)
                if method in results and work != results[method]:
                    raise ArithmeticError('deterministic replay differs')
                results[method] = work
        incidental = {m: scan(n, 320, 256, m == 'filtered', audit_gcds=True)['incidental_factor']
                      for m in ('all','filtered')}
        for key in ('first_root', 'target_factor'):
            restrict = lambda w: {k: v for k, v in (w or {}).items() if k != 'visits'}
            if restrict(results['all'][key]) != restrict(results['filtered'][key]):
                raise ArithmeticError('filter removed a targeted result')
        for result in results.values():
            hit = result['target_factor']
            if hit and (n % int(hit['value']) or decimal in expected and hit['value'] not in expected[decimal]):
                raise ArithmeticError('discovered factor failed the independent check')
        rows.append(dict(n=decimal, panel=panel, bits=bits, results=results, cpu_ns=timings, incidental_gcd_audit=incidental))
    summary = []
    for bits in (20, 24):
        selected = [r for r in rows if r['bits'] == bits and r['panel'] == 'validation']
        summary.append(dict(bits=bits, held_out_inputs=len(selected),
                            root_hits=sum(bool(r['results']['filtered']['first_root']) for r in selected),
                            target_splits=sum(bool(r['results']['filtered']['target_factor']) for r in selected),
                            methods={m: dict(steps=sum(r['results'][m]['steps'] for r in selected),
                                             median_cpu_ns=int(median(sum(r['cpu_ns'][m][i] for r in selected)
                                                                     for i in range(4))))
                                     for m in ('all','filtered')}))
    return dict(multiplier_limit=320, steps_per_multiplier=256, timings='Process CPU nanoseconds including all target-search setup; separate all-row gcd diagnostic untimed.',
                rows=rows, held_out_summaries=summary)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    s = json.dumps(report(), indent=2)
    if args.output:
        args.output.write_text(s+'\n')
    else:
        print(s)
