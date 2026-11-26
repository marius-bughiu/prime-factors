"""Apply the canonical shortest-period mask to the fixed 32-product validation set.

The original comparison supplies only a public draw number and product to the
search. Baseline counters and independently checked prime labels are joined
after discovery. The optional --check replay checks the same complete Lean
certificate for each recovered pair, including an extra shortest-period hit
on the row where the fixed Jacobi evaluator stopped before interpolation.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path

from .character_column_backends import compare
from .character_growing_validation import BUDGET, MODE, RECORD as SOURCE, ROOT, WHEEL, costs

RECORD = ROOT/'research/least-period-growing.json'


def panel(baseline, *, replay):
    from scripts.factor import render_certificate, verify_file
    totals = {k:Counter() for k in ('ordinary','jacobi','shortest')}
    sources = Counter()
    rows=[]
    for item in baseline['rows']:
        n=int(item['n'])
        plan,_=compare(n,clipped=True,least_period=True,wheel=WHEEL,max_work=BUDGET,
                       modes=(MODE,),diagnostics=False)
        run=plan['runs'][MODE]
        prep=plan['selection']
        charges=costs(plan,run)
        # Class formation computes y=N*inv(x) mod M. A local modular power is
        # counted as a single square-class test. Trial factoring small periods
        # and integer comparisons are outside this uniform arithmetic tally.
        charges.update(selector_inversions=prep['inverses'],selector_pairing=2*prep['inverses'],
                       selector_square_tests=prep['square_tests'])
        sources.update(charges)
        factor=run['factor']
        row=dict(draw=item['draw'],period=plan['period'],canonical=plan.get('canonical'),offsets=plan['rho'],
                 planned=run['planned_work'],outcome=run['outcome'],factor=str(factor) if factor else None,
                 visited=run['visited'],unvisited=run['unvisited'],convolution_inputs=run['work'].get(
                     'convolution_input_coefficients',0),arithmetic_units=sum(charges.values()))
        if factor:
            if not 1<factor<n or n%factor:
                raise ArithmeticError('invalid readout')
            pair=sorted((factor,n//factor))
            proof=render_certificate(n,pair,certificate_trial_limit=1<<15)
            digest=sha256(proof.encode()).hexdigest()
            if digest!=item.get('certificate_sha256'):
                raise ArithmeticError('pair does not match the independently checked public product certificate')
            if replay:
                path=ROOT/'build/least-period-growing'/f'{n}.lean'
                path.parent.mkdir(exist_ok=True,parents=True)
                path.write_text(proof)
                verify_file(path)
            row.update(certificate_sha256=digest,remaining=[])
        else:
            row.update(remaining=[str(n)])
        rows.append(row)
        for key,data in (('ordinary',item['ordinary']),('jacobi',item['clipped']),('shortest',row)):
            totals[key].update(splits=int(bool(data['factor'])), convolution_inputs=data['convolution_inputs'],
                               arithmetic_units=data['arithmetic_units'])
    return dict(source=SOURCE.name, mode=MODE,wheel=WHEEL,max_work=BUDGET,reflect=False,
                totals={k:dict(v) for k,v in totals.items()},shortest_sources=dict(sources),rows=rows)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    group=parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--write',action='store_true')
    group.add_argument('--check',action='store_true')
    args=parser.parse_args()
    actual=panel(json.loads(SOURCE.read_text()),replay=args.check)
    if args.write:
        RECORD.write_text(json.dumps(actual,indent=2)+'\n')
    elif actual!=json.loads(RECORD.read_text()):
        raise SystemExit('deterministic results differ')
