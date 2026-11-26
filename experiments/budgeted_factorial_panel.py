"""Replay the fixed 96-bit centered search with a convolution-input budget.

Use --inputs for the public sample commitment. Both --write and --check run
the product-only search and replay the Lean certificate of every discovered
pair. The cap counts input coefficients across convolutions. Seed products,
checkpoint gcds and table setup have separate work counters. Timings cover
search only and are excluded from reproducibility checks.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
from time import process_time_ns

from experiments.affine_radix_holdout import draw_prime
from experiments.growing_factorial import search
from scripts.factor import render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]
SUMMARY = ROOT / 'research/budgeted-factorial-panel.json'
RECEIPTS = ROOT / 'build/budgeted-factorial-panel-proofs'
SEED = b'budgeted-factorial-96-v1'
WIDTH = 48
SAMPLE = 8
MAX_INPUTS = 1_100_000
WHEEL = 210


def draws():
    seen = set()
    rows = []
    index = 0
    while len(rows) < SAMPLE:
        p, q = sorted(draw_prime(side, index, bits=WIDTH, seed=SEED) for side in (b'p', b'q'))
        n = p*q
        if n.bit_length() == 2*WIDTH and p != q and n not in seen:
            rows.append((index, n, (p, q)))
            seen.add(n)
        index += 1
    return rows


def protocol(sample):
    inputs = ''.join(f'{index} {n}\n' for index, n, _ in sample).encode('ascii')
    return dict(seed=SEED.decode(), prime_bits=WIDTH, sample_size=SAMPLE,
                rule='First distinct full-width products of distinct primes, in ascending draw order.',
                public_inputs_sha256=sha256(inputs).hexdigest(), wheel=WHEEL,
                mode='centered', final_grid=True, max_span=None, max_inputs=MAX_INPUTS)


def panel(sample):
    RECEIPTS.mkdir(exist_ok=True, parents=True)
    rows, times = [], []
    for index, n, generated in sample:
        start = process_time_ns()
        run = search(n, None, wheel=WHEEL, folded=True, final_grid=True, max_inputs=MAX_INPUTS)
        elapsed = process_time_ns()-start
        factor = run.pop('factor')
        ranges = [tuple(map(int, interval)) for interval in run['ranges']]
        hit = any(low <= generated[0] <= high for low, high in ranges)
        if run['outcome'] in ('prefix_gcd', 'convolution_limit') and hit != (factor is not None):
            raise ValueError(f'discovered result does not match the checked ranges on draw {index}')
        row = dict(draw=index, n=str(n), **run, factors=[], remaining=[str(n)])
        width = int(run['upper'])-int(run['low'])+1
        row['unvisited_span'] = str(width-int(run['covered_span']))
        if factor is not None:
            recovered = sorted((factor, n//factor))
            if tuple(recovered) != generated:
                raise ValueError(f'wrong factors on draw {index}')
            source = render_certificate(n, recovered, certificate_trial_limit=1<<20)
            path = RECEIPTS/f'{n}.lean'
            path.write_text(source)
            verify_file(path)
            row.update(factors=list(map(str, recovered)), remaining=[],
                       certificate_sha256=sha256(source.encode()).hexdigest())
        print(f'draw {index}: {run["outcome"]}, covered {run["covered_span"]}, '
              f'{run["work"].get("convolution_input_coefficients",0)} inputs, '
              f'{elapsed/1e9:.3f} CPU seconds', flush=True)
        rows.append(row)
        times.append(elapsed)
    return dict(protocol=protocol(sample), rows=rows, search_cpu_ns=times)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    for name in ('inputs', 'write', 'check'):
        mode.add_argument('--'+name, action='store_true')
    args = parser.parse_args()
    sample = draws()
    if args.inputs:
        print(json.dumps(dict(protocol=protocol(sample),
                              inputs=[[index,str(n)] for index,n,_ in sample]), indent=2))
        return
    results = panel(sample)
    if args.write:
        SUMMARY.write_text(json.dumps(results, indent=2)+'\n')
    else:
        previous = json.loads(SUMMARY.read_text())
        for report in (previous, results):
            report.pop('search_cpu_ns')
        if previous != results:
            raise SystemExit('budgeted factorial replay differs from stored results')


if __name__ == '__main__':
    main()
