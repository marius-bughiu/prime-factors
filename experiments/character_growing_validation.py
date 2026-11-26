"""Predeclared independent validation of one Jacobi-column configuration.

Visit draws in increasing order, ordinary then clipped on each. Neither
planned work nor character selection has access to the sampling labels.
All arithmetic source counts below are obtained from the executed growing
forward schedule, independently of the conservative charge before launch.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
from time import process_time

from .affine_radix_holdout import draw_prime
from .character_column_backends import compare

SEED = b'character-growing-210-validation-v1'
COUNT = 32
WHEEL = 210
BUDGET = 2_000_000
MODE = 'growing_forward'
ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT/'research/character-growing-validation.json'


def draws():
    seen = set()
    draw = 0
    while len(seen) < COUNT:
        pair = tuple(sorted(draw_prime(side, draw, bits=30, seed=SEED) for side in (b'p',b'q')))
        n = pair[0]*pair[1]
        if pair[0] != pair[1] and n.bit_length()==60 and n not in seen:
            seen.add(n)
            yield draw, n, pair
        draw += 1


def costs(plan, run):
    """Count explicit arithmetic, separate from convolution and operand sizes.

    Count integer products (including sign products) and modular reductions at
    the places they occur. A packed Decimal multiplication, a modular inverse,
    a gcd, and a Jacobi-symbol call are each recorded as one operation. Decimal
    input formatting and output decoding are also reported in coefficients.
    Loop control, mask comparisons, memory and planning are outside the tally.
    """
    w = Counter(run['work'])
    conv = w['convolutions']
    inputs = w['convolution_input_coefficients']
    shifts = w['shifted_values']
    # Sum of d+1 across shifts, since I = (d+1)+last and shifted=last-d.
    weights, rem = divmod(inputs-shifts+conv,2)
    if rem:
        raise ArithmeticError('inconsistent interpolation counters')
    recip = inputs-weights
    decoded = inputs-conv
    if w['setup_gcds']!=w['inversions']:
        raise ArithmeticError('table-denominator collision outside this 30-bit prime protocol')
    table = 2*w['peak_table_index']-w['inversions']
    paired = w['paired_products']
    seed = w['seed_terms']
    checkpoints = w['checkpoint_multiplications']
    if w['direct_candidates'] > checkpoints:
        raise ArithmeticError('direct endpoint products missing from checkpoint charges')
    # Each arithmetic source counts products plus corresponding reductions.
    # Weights: three products (the last by ±1), one reduction. Rescaling:
    # two products and a reduction per new sample. Table + reciprocal entries
    # each take one product and one reduction.
    sources = dict(
        seed=2*seed,
        table=2*table,
        interpolation=4*weights+2*recip+3*shifts,
        convolution=inputs+2*decoded+conv,  # format inputs, decode and reduce outputs, packed products
        doublings=2*paired,
        checkpoints=2*checkpoints,
        backend_gcds=(w['wheel_gcds']+w['offset_validation_gcds']
                      +w['setup_gcds']+w['checkpoint_gcds']),
        inversions=w['inversions'],
        selector_gcds=sum(v for k,v in plan['selection'].items() if k.endswith('gcds'))
                      +plan['mask_rebuild_gcds'],
        selector_jacobi=sum(v for k,v in plan['selection'].items() if 'jacobi' in k)
                        +plan['mask_rebuild_jacobi'],
    )
    return sources


def run_panel():
    from scripts.factor import render_certificate, verify_file
    rows, times = [], []
    totals = {s:Counter() for s in ('ordinary','clipped')}
    for draw, n, labels in draws():
        row = dict(draw=draw,n=str(n))
        elapsed = {}
        pairs = set()
        for target in ('ordinary','clipped'):
            started = process_time()
            plan, _ = compare(n,clipped=target=='clipped', max_work=BUDGET, wheel=WHEEL,
                              modes=(MODE,),diagnostics=False)
            elapsed[target] = process_time()-started
            run = plan['runs'][MODE]
            sources = costs(plan,run)
            work = Counter(run['work'])
            factor = run['factor']
            if factor is not None:
                if not 1 < factor < n or n % factor:
                    raise ArithmeticError('invalid factor readout')
                pairs.add(tuple(sorted((factor,n//factor))))
            row[target] = dict(d=plan['d'], sign=plan['sign'], outcome=run['outcome'],
                               factor=str(factor) if factor else None, visited=run['visited'],
                               unvisited=run['unvisited'], planned=run['planned_work'],
                               remaining=[] if factor else [str(n)],
                               convolution_inputs=work['convolution_input_coefficients'],
                               arithmetic_units=sum(sources.values()), sources=sources)
            totals[target].update(sources)
        if pairs:
            pair, = pairs
            if pair != labels:
                raise ArithmeticError('discovered pair differs from independent sample')
            # Each discovered prime has 30 bits. Its predecessor's trial
            # factors through 2^15 suffice for the independent Pratt proof.
            source = render_certificate(n,list(pair),certificate_trial_limit=1<<15)
            path = ROOT/'build/character-growing-validation'/f'{n}.lean'
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source)
            verify_file(path)
            row.update(factors=list(map(str,pair)), remaining=[], certificate_sha256=sha256(source.encode()).hexdigest())
        else:
            row.update(factors=[], remaining=[str(n)])
        rows.append(row)
        times.append(elapsed)
    return dict(seed=SEED.decode(), count=COUNT, prime_bits=30, product_bits=60, wheel=WHEEL,
                max_work=BUDGET, mode=MODE, final_grid=True, rows=rows,
                arithmetic_sources={k:dict(v) for k,v in totals.items()}, search_cpu_seconds=times)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    options=parser.add_mutually_exclusive_group(required=True)
    options.add_argument('--write',action='store_true')
    options.add_argument('--check',action='store_true')
    args = parser.parse_args()
    result = run_panel()
    if args.write:
        RECORD.write_text(json.dumps(result,indent=2)+'\n')
    else:
        expected = json.loads(RECORD.read_text())
        for item in (expected,result):
            item.pop('search_cpu_seconds')
        if result != expected:
            raise SystemExit('validation results differ')
