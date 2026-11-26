"""Compare complete and growing factorial blocks on the frozen Jacobi-column panel.

Both backends use the same original two-million-unit preflight plus a
conservative charge for the folded shift and growing checkpoints. Gcd,
inversion and packed convolution are charged as arithmetic operations, not
bit operations. Mask construction and the optional folding diagnostics are
reported separately. The folded polynomial in FoldedFactorial.lean applies
to any shared offset mask. An axis c tabulated here means precisely that
r -> c-r preserves the entire mask modulo the wheel. It does not identify
two roots of the folded polynomial modulo a prime factor of the input.
No expected factor is supplied to discovery.
"""
import argparse
from collections import Counter
import json
from math import gcd
from pathlib import Path
from time import process_time

from . import growing_factorial
from .character_divisor_column import RECORD as SOURCE, _before, _plan, search as select
from .factorial_progressions import block_products, decimal_convolution, folded_blocks
from .mixed_ratio_heights import jacobi

RECORD = Path(__file__).resolve().parents[1]/'research/character-column-backends.json'
MODES = ('complete_forward', 'complete_folded', 'growing_forward', 'growing_folded')


def reflection_axes(period, residues):
    """Every possible axis sends the first residue to one of the residues."""
    mask = set(residues)
    return sorted(c for c in ((residues[0]+r) % period for r in residues)
                  if all((c-r) % period in mask for r in residues))


def fold_diagnostic(n, period, residues, base, width, cycles, cap):
    """Test whether two offsets can share a root at a hidden prime above h*period.

    Their folded-root difference has numerator (r-s)(2*center-h*period+r+s).
    Thus one excludes a coincidence at both factors by a coprime interval
    product, provided the promised factors exceed the half-block stride.
    """
    axis = reflection_axes(period, residues)
    half = width//2
    center = base + (cycles//width)*half*period
    checks = []
    for h in dict.fromkeys((1, half) if half else ()):
        stride = h*period
        length = 2*stride-1
        result = dict(half_cycles=str(h), offsets=str(h*len(residues)), integers=str(length),
                      below_factor_floor=stride < (1 << ((n.bit_length()-1)//2)))
        if length+1 <= cap:
            cap -= length+1
            product = 1
            for term in range(2*center-stride, 2*center+stride-1):
                product = product*term % n
            result['gcd'] = str(gcd(product, n))
        checks.append(result)
    return dict(reflections=axis, root_checks=checks)


def work_bound(rho, width, cycles, edges, folded):
    """Bound setup, seed, shifts, doublings, checkpoints, edges of either run.

    Ten units per input cover signed weights, encoding/decoding, convolution
    output reduction and rescaling. Twelve per largest table index cover its
    forward/inverse entries, reciprocals and fallback gcds. Tables in the
    growing final-grid solver only grow. At most a full extra block per stage
    is checked across a previous checkpoint boundary.
    """
    count = cycles//width
    paired = folded and width > 1
    terminal = width//2 if paired else width
    size = 1
    total_inputs = total_values = largest_index = 0
    while size < terminal or (size == terminal == 1 and count > rho+1):
        step = min(2*size, terminal)
        next_count = count if step == terminal else rho*step+1
        last = (next_count-1) if step == size else 2*next_count-1
        degree = rho*size
        if last > degree:
            limit = last+degree+1 if paired else last
            inputs = 2*(degree+1)+limit if paired else degree+1+last
            total_inputs += inputs
            largest_index = max(largest_index, limit)
        total_values += next_count
        size = step
        if step == terminal:
            break
    return (12*(largest_index+1) + 10*total_inputs + 6*(total_values+count+edges)
            + 6*(rho+1)**2 + 12*width.bit_length())


def complete(n, low, high, period, residues, base, cycles, folded):
    work = Counter()
    blocks = []
    width = 1
    if cycles:
        evaluate = folded_blocks if folded else block_products
        blocks, width, divisor = evaluate(base, cycles, period, residues, n, decimal_convolution, work)
        if divisor is not None:
            return dict(outcome='interpolation_divisor' if divisor<n else 'nonunit_setup',
                        factor=divisor if divisor<n else None, visited='0', work=dict(work))
    product = 1
    for value in blocks:
        product = product*value % n
    work['block_accumulations'] = len(blocks)
    work['batched_candidates'] = len(blocks)*width*len(residues)
    end = base+len(blocks)*width*period
    for lo, hi in ((low, min(base, high)), (end+1, high)):
        for start in range(lo//period*period, hi+1, period):
            for r in residues:
                if lo <= start+r <= hi:
                    work['edge_candidates'] += 1
                    product = product*(start+r) % n
    factor = gcd(product, n)
    work['final_gcds'] = 1
    return dict(factor=factor if 1<factor<n else None, product=str(product),
                outcome='product_gcd' if 1<factor<n else ('whole_modulus' if factor==n else 'no_split'),
                visited=str(work['batched_candidates']+work['edge_candidates']), work=dict(work))


def compare(n, *, clipped, max_work=2_000_000, wheel=30, modes=MODES, diagnostics=True,
            least_period=False):
    if max_work < 0:
        raise ValueError('expected a nonnegative arithmetic work cap')
    if any(mode not in MODES for mode in modes):
        raise ValueError('unknown comparison mode')
    residues = None
    if least_period:
        from .separating_period import select_mask
        if not clipped:
            raise ValueError('least-period mode selects a mask on the clipped interval')
        choice, lo, hi, residues = select_mask(n, wheel=wheel, max_work=max_work)
        choice.update(d=None, sign=None)
        if residues is not None:
            choice.update(lower=lo, upper=hi)
    else:
        choice = select(n, max_work=0, ordinary=not clipped, clip=clipped, wheel=wheel)
    if 'lower' not in choice:
        runs = {mode:dict(outcome=choice['outcome'], factor=choice['factor'], visited='0',
                          unvisited=None, planned_work=None, work={}) for mode in modes}
        return dict(d=choice['d'], sign=choice['sign'], period=None, rho=None, candidates=None,
                    selection=choice['selection'], mask_rebuild_gcds=0, mask_rebuild_jacobi=0,
                    checks=None, runs=runs), {}
    lo, hi = int(choice['lower']), int(choice['upper'])
    period = choice['period']
    rebuild_gcds = rebuild_jacobi = 0
    if residues is None:
        units = [i for i in range(1, period) if gcd(i,period)==1]
        residues = [i for i in units if jacobi(choice['d'],i)==choice['sign']] if clipped else units
        rebuild_gcds, rebuild_jacobi = period-1, len(units) if clipped else 0
    base, cycles, width, candidates, original = _plan(lo, hi, period, residues)
    edges = candidates - (cycles//width)*width*len(residues)
    report = dict(d=choice['d'], sign=choice['sign'], period=period, rho=len(residues),
                  candidates=str(candidates), selection=choice['selection'],
                  mask_rebuild_gcds=rebuild_gcds, mask_rebuild_jacobi=rebuild_jacobi,
                  checks=(fold_diagnostic(n, period, residues, base, width, cycles, max_work)
                          if diagnostics else None),
                  runs={})
    if least_period:
        report['canonical'] = choice['canonical']
    times = {}
    for mode in modes:
        folded = mode.endswith('folded')
        charge = max(original, work_bound(len(residues),width,cycles,edges,folded))
        if charge > max_work:
            run = dict(outcome='work_limit', factor=None, visited='0', work={})
        else:
            started = process_time()
            if mode.startswith('complete'):
                run = complete(n, lo, hi, period, residues, base, cycles, folded)
            else:
                result = growing_factorial.search(n, None, wheel=period, bounds=(lo,hi), offsets=residues,
                                                  folded=folded, final_grid=True)
                run = {key:result[key] for key in ('outcome','factor','ranges','work')}
                run['visited'] = str(sum(_before(int(b)+1, period, residues)-_before(int(a),period,residues)
                                         for a,b in result['ranges']))
            times[mode] = process_time()-started
        run.update(planned_work=str(charge), unvisited=str(candidates-int(run['visited'])))
        report['runs'][mode] = run
    return report, times


def panel():
    from scripts.factor import render_certificate, verify_file
    from hashlib import sha256
    baseline = json.loads(SOURCE.read_text())
    rows, times = [], []
    for old in baseline['rows']:
        n = int(old['n'])
        row = {'id':old['id'], 'n':old['n']}
        elapsed = {}
        found = set()
        for wheel in (baseline['wheel'], 210):
            wheel_key = f'wheel_{wheel}'
            row[wheel_key], elapsed[wheel_key] = {}, {}
            for target in ('ordinary','clipped'):
                data, clock = compare(n, clipped=(target=='clipped'), wheel=wheel,
                                      max_work=baseline['max_work'])
                elapsed[wheel_key][target] = clock
                column = {key:data[key] for key in ('d','sign','period','rho','candidates','checks')}
                row[wheel_key][target] = column
                for mode, run in data['runs'].items():
                    if run['factor'] is not None:
                        factor = run['factor']
                        if not 1 < factor < n or n % factor:
                            raise ArithmeticError('not a proper divisor')
                        found.add(tuple(sorted((factor,n//factor))))
                    if mode.startswith('complete') and 'product' in run:
                        expected = (old[target]['product'] if wheel==baseline['wheel']
                                    else data['runs']['complete_forward']['product'])
                        if run['product'] != expected or int(run['unvisited']):
                            raise ArithmeticError('complete products disagree')
                    column[mode] = {k:run[k] for k in ('factor','outcome','visited','planned_work')}
                    column[mode].update(convolution_inputs=run['work'].get('convolution_input_coefficients',0),
                                        table_limit=run['work'].get('factorial_limit',0),
                                        checkpoints=run['work'].get('checkpoint_gcds',0))
        if found:
            pair, = found
            source = render_certificate(n, list(pair))
            digest = sha256(source.encode()).hexdigest()
            if digest != old['certificate_sha256']:
                raise ArithmeticError('discovered pair differs from the frozen proof')
            path = SOURCE.parents[1]/'build/character-column-backends'/f'{n}.lean'
            path.parent.mkdir(exist_ok=True, parents=True)
            path.write_text(source)
            verify_file(path)
            row.update(factors=list(map(str,pair)), remaining=[],certificate_sha256=digest)
        else:
            row.update(factors=[], remaining=[str(n)])
        rows.append(row)
        times.append(elapsed)
    return dict(source=SOURCE.name, wheels=[baseline['wheel'],210], max_work=baseline['max_work'],
                diagnostic_cap=baseline['max_work'], rows=rows, search_cpu_seconds=times)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    action=parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--write',action='store_true')
    action.add_argument('--check',action='store_true')
    args = parser.parse_args()
    result = panel()
    if args.write:
        RECORD.write_text(json.dumps(result,indent=2)+'\n')
    else:
        old=json.loads(RECORD.read_text())
        old.pop('search_cpu_seconds')
        result.pop('search_cpu_seconds')
        if result!=old:
            raise SystemExit('deterministic results differ')
