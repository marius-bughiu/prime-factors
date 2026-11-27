"""Compute the sixteen-character finite-window cap from the two public balanced products.

Scan 2^20 continued-fraction steps for each product. The common anchor selector
visits distinct available moduli in increasing order, retaining each modulus
coprime to 60 and the product of all earlier selections, until it has sixteen.
The rate below is relative to the smaller-factor positions in the unit lanes
modulo 60, assuming the two factors are 1024-bit primes.
"""

import argparse
from fractions import Fraction
import json
from math import gcd, isqrt
from pathlib import Path

from experiments.reciprocal_anchor import collect_anchors, progressions


ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'research/many-character-windows.json'
COUNT = 16
STEPS = 1 << 20
WHEEL = 60
SCALE = 1_000_000


def ceil_div(a, b):
    return (a+b-1)//b


def cases():
    source = ROOT / 'benchmarks/reciprocal-anchors.json'
    cases = json.loads(source.read_text())
    return [case for case in cases if case['factor_bits'] == 1024 and int(case['n']).bit_length() == 2048]


def measure(case):
    n = int(case['n'])
    bits = case['factor_bits']
    maximum_prime = (1 << bits)-1
    lo, hi = ceil_div(n, maximum_prime), isqrt(n)
    units = [r for r in range(WHEEL) if gcd(r, WHEEL) == 1]
    lengths = [length for _, length in progressions(lo, hi, units, WHEEL)]
    least = (hi-lo+1)//WHEEL
    if len(lengths) != len(units) or least <= 0 or any(length not in (least, least+1) for length in lengths):
        raise ArithmeticError('wheel lanes disagree with the certified interval')
    anchors = collect_anchors(n, steps=STEPS, wheel=WHEEL, count=COUNT)
    if len(anchors) != COUNT:
        raise ArithmeticError('the fixed public budget did not supply sixteen periods')
    moduli = [a['period'] for a in anchors]
    if moduli != sorted(moduli) or len(set(moduli)) != COUNT:
        raise ArithmeticError('the selected moduli must be distinct and ordered')
    for i, anchor in enumerate(anchors):
        d = anchor['period']
        if d % 4 != 3 or gcd(d,n*WHEEL) != 1 or any(gcd(d,q) != 1 for q in moduli[:i]):
            raise ArithmeticError('moduli are not pairwise coprime or fail the wheel conditions')
        if (anchor['minus_root']**2+d) % n or (anchor['root']**2-n) % d:
            raise ArithmeticError('a public square-root certificate failed')
    radii = [isqrt(d-1)+1 for d in moduli]
    height = max(d.bit_length() for d in moduli)
    c1, c2 = (ceil_div(5220 + m*347*height, 2220) for m in (1,2))
    r_sum = sum(radii)
    square_sum = sum(r*r for r in radii)
    weighted = [Fraction((t*t+COUNT)*(least+1) + 2*t*c1*r_sum + c2*(r_sum*r_sum-square_sum),
                         (t+COUNT)**2*least) for t in range(COUNT+1)]
    # Optimize the exact rational upper bound before rounding it to ppm.
    # The first minimizing integer wins a tie.
    best = min(range(COUNT+1), key=weighted.__getitem__)
    ppm = [ceil_div(SCALE*b.numerator,b.denominator) for b in weighted]
    return dict(id=case['id'], n=str(n), factor_bits=bits,
                population='smaller factor of two 1024-bit primes with this 2048-bit product',
                wheel=WHEEL, wheel_lanes=len(units), lower=str(lo), upper=str(hi),
                min_lane_length=str(least), wheel_positions=str(sum(lengths)),
                cf_steps=STEPS, anchor_steps=[a['step'] for a in anchors],
                moduli=[str(d) for d in moduli], negative_roots=[str(a['minus_root']) for a in anchors],
                radii=[str(r) for r in radii], max_modulus_bits=height, c1=c1, c2=c2,
                radius_sum=str(r_sum), radius_square_sum=str(square_sum),
                t=best, ppm_by_t=ppm, certified_parts_per_million=ppm[best])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='replace the checked-in data with this run')
    args = parser.parse_args()
    records = []
    source = cases()
    if len(source) != 2:
        raise ValueError('expected the fresh and crossed 2048-bit fixtures')
    for case in source:
        row = measure(case)
        records.append(row)
        print(row['id'], 't', row['t'], 'ppm', row['certified_parts_per_million'], flush=True)
    if args.write:
        RESULTS.write_text(json.dumps(records, indent=2)+'\n')
    elif json.loads(RESULTS.read_text()) != records:
        raise ValueError('many-character bounds disagree with their stored results')


if __name__ == '__main__':
    main()
