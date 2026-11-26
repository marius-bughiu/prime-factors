"""Compare the same factorial-product evaluator on two public lower bounds."""
import argparse
import json
from pathlib import Path
from time import process_time

from .crt_holdout import draw_prime
from .factorial_progressions import search
from scripts.factor import primes_through, render_certificate, verify_file

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT/'research/short-pascal-panel.json'
SEED = b'short-pascal-fullwidth-v1'


def run(verify=False):
    primes = primes_through(1 << 20)
    rows = []
    times = []
    draw = 0
    while len(rows) < 8:
        p, q = sorted(draw_prime(SEED, side, draw, primes) for side in (b'p', b'q'))
        draw += 1
        n = p*q
        if p == q or n.bit_length() != 80:
            continue
        row = dict(draw=draw-1, n=str(n))
        elapsed = {}
        # Alternate order to distribute warm-up costs across the two methods.
        for tight in ((False, True) if len(rows)%2 == 0 else (True, False)):
            label = 'equal_width' if tight else 'ratio_only'
            start = process_time()
            actual = search(n, None, wheel=210, equal_width=tight)
            elapsed[label] = process_time()-start
            if not actual['interval_complete'] or actual['factor'] not in (p, q):
                raise ArithmeticError('completed scan did not recover the generated pair')
            counts = actual['work']
            row[label] = dict(lower=actual['low'], upper=actual['high'], span=actual['span'],
                              candidates=counts['batched_candidates']+counts.get('edge_candidates',0),
                              degree=counts['block_degree'], blocks=counts['blocks'],
                              convolution_inputs=counts['convolution_input_coefficients'],
                              product_residue=actual['product'])
        pair = sorted([actual['factor'], n//actual['factor']])
        row['factors'] = list(map(str,pair))
        if verify:
            directory = ROOT/'build/short-pascal-panel-proofs'
            directory.mkdir(parents=True, exist_ok=True)
            path = directory/f'{n}.lean'
            path.write_text(render_certificate(n,pair,certificate_trial_limit=1 << 20))
            verify_file(path)
        rows.append(row)
        times.append(elapsed)
        print(f"{n}: candidates {row['ratio_only']['candidates']} -> {row['equal_width']['candidates']}, "
              f"CPU seconds {elapsed['ratio_only']:.3f} -> {elapsed['equal_width']:.3f}", flush=True)
    return dict(seed=SEED.decode(), sample="First eight accepted distinct 40-bit prime pairs with an 80-bit product.",
                wheel=210, rows=rows), times


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    options = parser.add_mutually_exclusive_group(required=True)
    options.add_argument('--write', action='store_true')
    options.add_argument('--check', action='store_true')
    parser.add_argument('--verify', action='store_true', help='independently check all eight factorizations with Lean')
    args = parser.parse_args()
    result, times = run(verify=args.verify)
    body = json.dumps(result, indent=2)+'\n'
    if args.write:
        REPORT.write_text(body)
    elif body != REPORT.read_text():
        raise SystemExit('panel did not match the recorded inputs and work')
    print('Total CPU seconds', {k:round(sum(t[k] for t in times),3) for k in times[0]})
