"""Rebuild negative-root witnesses for two fixed products and conditional prime counts."""

import argparse
from hashlib import sha256
import json
from math import gcd, isqrt, prod
from pathlib import Path
from time import perf_counter_ns, process_time_ns

from experiments.many_character_window import cases, ceil_div
from experiments.reciprocal_anchor import collect_anchors


ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'research/split-prime-panel.json'
STEPS = 32_768
COUNT = 512
WHEEL = 60
ENDPOINT_COEFFICIENT = 121*COUNT*355 + 21_007
PRIME_POWER_COEFFICIENT = 710
INTERVAL_ERROR_BITS = 538
INTERVAL_ERROR = 1 << INTERVAL_ERROR_BITS


def select(n, stats=None):
    anchors = collect_anchors(n, STEPS, WHEEL, COUNT, negative_only=True, stats=stats)
    if len(anchors) != COUNT:
        raise ValueError(f'expected {COUNT} coprime moduli, got {len(anchors)}')
    return anchors


def full_panel(n):
    """Return all 512 (d, negative square root modulo n) pairs for the Lean receipt."""
    return [(a['period'], a['minus_root']) for a in select(n)]


def prime_count_bound(width, k):
    """Conditional character-sum estimate with interval error at most 2^538."""
    m = 1 << k
    lower = max(0, ceil_div(width-m*INTERVAL_ERROR, m*710))
    upper = (width+m*INTERVAL_ERROR)//(m*708)
    return lower, upper


def measure(case):
    n, bits = int(case['n']), case['factor_bits']
    setup = {}
    start_wall, start_cpu = perf_counter_ns(), process_time_ns()
    anchors = select(n, setup)
    setup_cpu = process_time_ns()-start_cpu
    setup_wall = perf_counter_ns()-start_wall
    moduli = [a['period'] for a in anchors]
    if moduli != sorted(set(moduli)):
        raise ArithmeticError('selected moduli must increase strictly')
    cumulative = 1
    digest = sha256()
    for anchor in anchors:
        d, x = anchor['period'], anchor['minus_root']
        if d % 4 != 3 or gcd(d,WHEEL*n) != 1 or gcd(d,cumulative) != 1:
            raise ArithmeticError('invalid discriminant or noncoprime selection')
        if (x*x+d) % n:
            raise ArithmeticError('invalid negative root')
        cumulative *= d
        digest.update(f'{d},{x}\n'.encode('ascii'))
    lo, hi = ceil_div(n,(1 << bits)-1), isqrt(n)
    width = hi-lo+1
    if (2*ENDPOINT_COEFFICIENT+PRIME_POWER_COEFFICIENT) * (1 << 512) > INTERVAL_ERROR:
        raise ArithmeticError('endpoint and prime-power error exceeds the stated interval budget')
    counts = []
    for k in (0,16,400,512):
        lower, upper = prime_count_bound(width, k)
        counts.append(dict(k=k, max_modulus_bits=max((d.bit_length() for d in moduli[:k]), default=0),
                           product_modulus_bits=prod(moduli[:k]).bit_length(),
                           lower=str(lower), upper=str(upper)))
    return dict(id=case['id'], n=str(n), factor_bits=bits, lower=str(lo), upper=str(hi),
                interval_width=str(width), cf_steps=STEPS, wheel=WHEEL, count=COUNT,
                selection=setup, max_modulus_bits=max(d.bit_length() for d in moduli),
                checked_negative_roots=COUNT, implied_coprime_pairs=COUNT*(COUNT-1)//2,
                anchor_steps=[a['step'] for a in anchors], witnesses_sha256=digest.hexdigest(),
                endpoint_coefficient=ENDPOINT_COEFFICIENT, prime_power_coefficient=PRIME_POWER_COEFFICIENT,
                coefficient_scale_log2=512, interval_error_log2=INTERVAL_ERROR_BITS,
                bound_assumption=('Grenié–Molteni Corollary 1.2 under Dirichlet GRH for the '
                                  'multiquadratic field; endpoint and prime-power derivation in discovery'),
                prime_counts=counts, setup_cpu_ns=setup_cpu, setup_wall_ns=setup_wall)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='regenerate compact witness data and timings')
    args = parser.parse_args()
    records = [measure(c) for c in cases()]
    if args.write:
        RESULTS.write_text(json.dumps(records,indent=2)+'\n')
    else:
        saved = json.loads(RESULTS.read_text())
        def deterministic(row):
            return {k:v for k,v in row.items() if k not in ('setup_cpu_ns','setup_wall_ns')}
        if list(map(deterministic, records)) != list(map(deterministic, saved)):
            raise ValueError('public witnesses or conditional candidate bounds changed')
    for row in records:
        print(row['id'], row['count'], 'negative roots,', row['max_modulus_bits'],
              'maximum modulus bits,', round(row['setup_cpu_ns']/1e9,3), 'CPU seconds')


if __name__ == '__main__':
    main()
