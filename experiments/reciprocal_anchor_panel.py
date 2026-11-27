"""Compare nested, product-selected residue tests on fixed positions in the balanced intervals."""
import json
from bisect import bisect_right
from itertools import accumulate
from math import gcd, isqrt, prod
from pathlib import Path
from random import Random
from time import process_time

from experiments.reciprocal_anchor import collect_anchors, jacobi, oriented, progressions, sum_bounds

ROOT = Path(__file__).resolve().parents[1]


def sample_positions(rows, rng, count):
    cumulative = list(accumulate(length for _, length in rows))
    draws = []
    for _ in range(count):
        index = rng.randrange(cumulative[-1])
        lane = bisect_right(cumulative, index)
        offset = index - (cumulative[lane-1] if lane else 0)
        draws.append(rows[lane][0]+60*offset)
    return draws


def run(n, mode, anchors, rows, count, seed):
    candidates = sample_positions(rows, Random(seed), count)
    full_check = (lambda x: n % x == 0) if mode == 'divisors' else (
        lambda s: isqrt(s*s-4*n)**2 == s*s-4*n)
    start = process_time()
    baseline = [x for x in candidates if full_check(x)]
    direct_seconds = process_time()-start
    start = process_time()
    remaining = candidates
    sizes = []
    evaluations = 0
    for anchor in anchors:
        d, e = anchor['period'], anchor['root']
        evaluations += len(remaining)
        if mode == 'divisors':
            remaining = [x for x in remaining if jacobi(x, d) == 1]
        else:
            remaining = [s for s in remaining if oriented(s, d, e)]
        sizes.append(len(remaining))
    matches = [x for x in remaining if full_check(x)]
    gated_seconds = process_time()-start
    if matches != baseline:
        raise ArithmeticError('a factor or an exact square was lost')
    return dict(draws=count, seed=seed, survivors=sizes, character_tests=evaluations,
                exact_tests=len(remaining), matches=[str(v) for v in matches],
                direct_cpu_seconds=round(direct_seconds,6), gated_cpu_seconds=round(gated_seconds,6))


def compare(n, bits=1024, steps=32768, count=4096):
    wheel = 60
    start = process_time()
    anchors = collect_anchors(n, steps, wheel, 8)
    if len(anchors) != 8:
        raise ValueError('the pinned panel requires eight coprime periods')
    setup = process_time()-start
    units = [i for i in range(wheel) if gcd(i,wheel)==1]
    cap = 2**bits-1
    divs = list(progressions((n+cap-1)//cap, isqrt(n), units, wheel))
    low,_,high = sum_bounds(n,bits)
    classes = {(i+n*pow(i,-1,wheel)) % wheel for i in units}
    sums = list(progressions(low, high, classes, wheel))
    return dict(steps=steps, period_bits=[a['period'].bit_length() for a in anchors],
                combined_period_bits=prod(a['period'] for a in anchors).bit_length(),
                setup_cpu_seconds=round(setup,6),
                divisors=run(n,'divisors',anchors,divs,count,240927),
                sums=run(n,'sums',anchors,sums,count,240928))


if __name__ == '__main__':
    cases = json.loads((ROOT/'benchmarks'/'reciprocal-anchors.json').read_text())
    print(json.dumps({c['id']:compare(int(c['n'])) for c in cases if c['factor_bits']==1024}, indent=2))
