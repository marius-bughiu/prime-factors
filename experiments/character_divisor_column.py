"""Evaluate one separating Jacobi column with the existing forward factorial blocks.

The input promise is a product of two distinct odd primes of equal bit length.
A negative (d/N) means the two primes lie in opposite character classes. A prime
in [B,2B) divides its own entry only. A completed product for either class
therefore has gcd equal to one prime. See factorial_progressions.py for the
existing interpolation and its sources.
"""
import argparse
from bisect import bisect_left
from collections import Counter
import json
from math import gcd, lcm
from pathlib import Path
from time import process_time

from .factorial_progressions import block_products, block_size, decimal_convolution
from .mixed_ratio_heights import jacobi
from .short_pascal_row import interval

DISCRIMINANTS = (-1, 2, -2, 3, -3, 5, -5, 7, -7, 11, -11)
MAX_PERIOD = 8192
ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / 'research/character-divisor-comparison.json'


def _before(stop, period, residues):
    cycles, tail = divmod(stop, period)
    return cycles * len(residues) + bisect_left(residues, tail)


def _plan(low, high, period, residues):
    """Conservatively charge the existing block_products before allocating.

    The cap charges explicit modular multiplications/reductions and convolution
    input/output coefficients. A packed Decimal multiplication, inversion and
    each gcd cost one additional unit; their internal bit operations are not
    estimated. The residue sieve and witness search have separate bounded costs.
    """
    rho = len(residues)
    candidates = _before(high+1, period, residues) - _before(low, period, residues)
    base = (low+period-2)//period*period
    cycles = max(0, (high-base)//period)
    width = block_size(cycles, rho)
    count = cycles//width
    edges = candidates-count*width*rho
    # Two units per modular multiply followed by reduction, one final gcd.
    cost = 2*(edges+count)+1
    if not cycles or (width == 1 and count <= rho+1):
        return base, cycles, width, candidates, cost + 2*count*rho

    # Solver setup: up to two factorial-table products per index, one
    # inversion, and up to limit gcds if a factorial shares both primes.
    limit = max(rho, rho*width+1 if width>2 else 0, 2*count-1 if width>1 else count-1)
    cost += 5*limit + 2 + 2*(rho+1)*rho

    def shift(degree, last):
        if last <= degree:
            return 0
        # Build signed weights and reciprocals, encode both convolution
        # inputs, reduce the full output, and rescale each new value.
        return (4*(degree+1) + 2*last + (degree+1+last) + 1
                + 2*(degree+last) + 3*(last-degree))

    if width == 1:
        cost += shift(rho, count-1)
    else:
        size = 1
        while size < width:
            new_size = 2*size
            needed = count if new_size == width else rho*new_size+1
            cost += shift(rho*size, 2*needed-1) + 2*needed
            size = new_size
    return base, cycles, width, candidates, cost


def _evaluate(n, low, high, period, residues, budget, report):
    work = Counter()
    base, cycles, width, total, charge = _plan(low, high, period, residues)
    report.update(lower=str(low), upper=str(high), period=period, residues=len(residues),
                  candidates=str(total), visited='0', unvisited=str(total), work=work,
                  planned_block_work=str(charge), max_work=budget)
    if charge > budget:
        report['outcome'] = 'work_limit'
        return report
    value = 1
    end = base
    if cycles:
        blocks, width, found = block_products(base, cycles, period, residues, n,
                                             decimal_convolution, work)
        if found is not None:
            if 1 < found < n:
                report.update(factor=found, outcome='interpolation_divisor')
            else:
                report['outcome'] = 'nonunit_setup'
            return report
        for block in blocks:
            value = value*block % n
        work['block_accumulations'] = len(blocks)
        work['batched_candidates'] = len(blocks)*width*len(residues)
        end += len(blocks)*width*period
    for lo, hi in ((low, min(high, base)), (end+1, high)):
        if lo > hi:
            continue
        for start in range(lo//period*period, hi+1, period):
            for residue in residues:
                candidate = start+residue
                if lo <= candidate <= hi:
                    value = value*candidate % n
                    work['edge_candidates'] += 1
    visited = work['edge_candidates'] + work['batched_candidates']
    if visited != total:
        raise ArithmeticError('the computed block and edge coverage differs from the plan')
    factor = gcd(n, value)
    work['final_gcds'] = 1
    report.update(visited=str(visited), unvisited='0', product=str(value),
                  outcome=('interval_gcd' if report['mode'] == 'ordinary' else 'column_gcd')
                  if 1 < factor < n else ('whole_modulus' if factor == n else 'no_split'),
                  factor=factor if 1 < factor < n else None)
    return report


def search(n, *, wheel=30, max_work=2_000_000, discriminants=DISCRIMINANTS,
           clip=False, ordinary=False):
    """Choose the smaller sign class by exact position count, breaking ties toward -1.

    ordinary=True is the matched existing forward factorial evaluator on the
    feasible smaller-prime interval, with the same preflight cap. clip=True
    intersects the whole octave with public bounds on either partner.
    """
    if n < 3 or n%2 == 0 or not 2 <= wheel <= MAX_PERIOD or max_work < 0:
        raise ValueError('expected odd n >= 3, a bounded wheel >= 2 and a nonnegative work cap')
    if ordinary and clip:
        raise ValueError('clipping applies to the character column')
    low, root = interval(n)
    B = 1 << ((n.bit_length()-1)//2)
    prep = Counter()
    report = dict(mode='ordinary' if ordinary else ('clipped' if clip else 'full'),
                  factor=None, outcome=None, d=None, sign=None,
                  period=None, visited='0', product=None, selection=prep, work={})
    prep['wheel_gcds'] += 1
    common = gcd(n, wheel)
    if common != 1:
        if common == n:
            for i in range(2, wheel+1):
                prep['wheel_gcds'] += 1
                part = gcd(i, n)
                if 1 < part < n:
                    return dict(report, factor=part, outcome='wheel_divisor')
            return dict(report, outcome='whole_modulus')
        return dict(report, factor=common, outcome='wheel_divisor')
    if ordinary:
        residues = [r for r in range(1, wheel) if gcd(r, wheel) == 1]
        prep['residue_gcds'] = wheel-1
        return _evaluate(n, low, root, wheel, residues, max_work, report)
    for d in discriminants:
        if not d or lcm(wheel, 4*abs(d)) > MAX_PERIOD:
            raise ValueError('zero numerator or requested character period too large')
        prep['jacobi_witness_tests'] += 1
        symbol = jacobi(d, n)
        if symbol == 0:
            prep['selector_gcds'] += 1
            part = gcd(n, d)
            if 1 < part < n:
                return dict(report, d=d, factor=part, outcome='selector_divisor')
        if symbol == -1:
            break
    else:
        return dict(report, outcome='no_witness')
    period = lcm(wheel, 4*abs(d))
    groups = {-1: [], 1: []}
    for r in range(1, period, 2):
        prep['residue_gcds'] += 1
        if gcd(r, period) == 1:
            prep['residue_jacobi_tests'] += 1
            groups[jacobi(d, r)].append(r)
    lo, hi = (low, min(2*B-1, n//B)) if clip else (B, 2*B-1)
    counts = {s: _before(hi+1, period, rs)-_before(lo, period, rs) for s,rs in groups.items()}
    sign = min(groups, key=lambda s: (counts[s], s))
    # Matching the wheel matters if d introduces another excluded prime.
    # On a full-width product, the clipped span is at least twice the smaller-
    # factor span minus one, since H+L >= 2*isqrt(n) for H=2B-1, L=ceil(n/H).
    # Each complete period has equally many units of each sign. Considering
    # the last partial period lets the column save at most one period's units.
    matched = sorted(groups[-1]+groups[1])
    smaller_count = _before(root+1, period, matched) - _before(low, period, matched)
    if len(groups[-1]) != len(groups[1]):
        raise ArithmeticError('a negative character must pair the two sign classes on the units')
    if n >= 2*B*B and counts[sign]+len(matched) < smaller_count:
        raise ArithmeticError('selected column violated the full-width counting bound')
    report.update(d=d, sign=sign, other_candidates=str(counts[-sign]),
                  matched_interval_candidates=str(smaller_count), matched_period_residues=len(matched))
    return _evaluate(n, lo, hi, period, groups[sign], max_work, report)


def panel():
    """The sample rule and budgets are fixed before examining any result."""
    from hashlib import sha256
    from .affine_radix_holdout import draw_prime
    from scripts.factor import render_certificate, verify_file

    seed = b'character-divisor-column-v1'
    proofs = ROOT/'build/character-divisor-column-proofs'
    proofs.mkdir(parents=True, exist_ok=True)
    samples = []
    draw = 0
    while len(samples)<8:
        p,q = sorted(draw_prime(side, draw, bits=30, seed=seed) for side in (b'p',b'q'))
        n = p*q
        if n.bit_length() == 60 and p != q and n not in {row[1] for row in samples}:
            samples.append((str(draw), n, (p,q)))
        draw += 1
    full_cases = json.loads((ROOT/'benchmarks/block-subresultant.json').read_text())
    samples.extend((c['id'], int(c['n']), None) for c in full_cases if int(c['n']).bit_length() == 2048)
    rows, times = [], []
    for i, (name, n, labels) in enumerate(samples):
        row = dict(id=name,n=str(n))
        elapsed = {}
        modes = ('ordinary','full','clipped')
        for mode in modes[i%3:]+modes[:i%3]:
            start = process_time()
            run = search(n, ordinary=mode=='ordinary', clip=mode=='clipped')
            elapsed[mode] = process_time()-start
            row[mode] = run
        factors = {r['factor'] for r in (row[m] for m in modes)} - {None}
        recovered = {tuple(sorted((d,n//d))) for d in factors}
        if len(recovered)>1 or (labels is not None and any(pair != labels for pair in recovered)):
            raise ArithmeticError('discovered factors disagree with the generated product')
        if recovered:
            pair, = recovered
            path = proofs/f'{n}.lean'
            source = render_certificate(n, list(pair))
            path.write_text(source)
            verify_file(path)
            row.update(factors=list(map(str,pair)),remaining=[],certificate_sha256=sha256(source.encode()).hexdigest())
        else:
            row.update(factors=[],remaining=[str(n)])
        rows.append(row)
        times.append(elapsed)
        print(name, *(row[m]['outcome'] for m in modes), flush=True)
    return dict(seed=seed.decode(), prime_bits=30, sample_size=8,
                sample='First eight distinct equal-width prime pairs giving a 60-bit product; then both published 2048-bit controls.',
                wheel=30, max_work=2_000_000, discriminants=list(DISCRIMINANTS), rows=rows, cpu_seconds=times)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    result = panel()
    if args.write:
        RECORD.write_text(json.dumps(result,indent=2)+'\n')
    else:
        expected = json.loads(RECORD.read_text())
        for item in (expected,result):
            item.pop('cpu_seconds')
        if result != expected:
            raise SystemExit('deterministic results differ from the published run')
