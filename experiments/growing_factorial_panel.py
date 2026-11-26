"""Compare three factorial searches on independent, predeclared equal-width draws.

Run python3 -m experiments.growing_factorial_panel --check --verify to repeat
the original three searches and kernel-check the recovered primes. Add --centered
for a separate fresh draw comparing folded complete and centered growing searches.
Use --final-grid for a third draw using the complete algorithm's terminal grid.
The latter two panels time each search in a new process to measure peak resident memory.
Replay checks deterministic work; CPU time and observed memory are machine-specific.
"""
import argparse
import json
import subprocess
import sys
from math import prod
from pathlib import Path
from time import process_time_ns

from .affine_radix_holdout import draw_prime as draw_wide_prime
from .crt_holdout import draw_prime
from .factorial_progressions import search as complete_search
from .growing_factorial import search as growing_search
from scripts.factor import primes_through, render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'research/growing-factorial-panel.json'
SEEDS = {40: b'prefix-factorial-ordinary-v1', 44: b'prefix-factorial-88-v1'}
CENTERED_SEEDS = {40: b'centered-prefix-factorial-heldout-v1', 44: b'centered-prefix-factorial-88-v1'}
CENTERED_REPORT = ROOT / 'research/centered-growing-factorial-panel.json'
CAPPED_SEEDS = {40: b'capped-folded-factorial-holdout-v1', 44: b'capped-folded-factorial-88-v1'}
CAPPED_REPORT = ROOT / 'research/capped-folded-factorial-panel.json'
METHODS = ('ordinary', 'folded', 'growing')
WHEEL = 210


def sample(seeds):
    trial_primes = primes_through(1 << 20)
    for bits, count in ((40, 8), (44, 1)):
        seen = set()
        draw = 0
        while len(seen) < count:
            seed = seeds[bits]
            pair = sorted(draw_prime(seed, side, draw, trial_primes) if bits == 40
                          else draw_wide_prime(side, draw, bits=bits, seed=seed)
                          for side in (b'p', b'q'))
            n = prod(pair)
            draw += 1
            if n.bit_length() != 2*bits or pair[0] == pair[1] or n in seen:
                continue
            seen.add(n)
            yield draw-1, n, pair


def evaluate(n, method):
    start = process_time_ns()
    if method == 'capped':
        run = growing_search(n, None, wheel=WHEEL, folded=True, final_grid=True)
    elif method == 'centered':
        run = growing_search(n, None, wheel=WHEEL, folded=True)
    elif method == 'growing':
        run = growing_search(n, None, wheel=WHEEL)
    else:
        run = complete_search(n, None, wheel=WHEEL, folded=method=='folded', equal_width=True)
    elapsed = process_time_ns()-start
    if method in ('growing', 'centered', 'capped'):
        high, covered = run['upper'], run['covered_span']
    else:
        if not run['interval_complete']:
            raise ArithmeticError('one-shot search did not consume the complete interval')
        high, covered = run['full_high'], run['span']
    factor = run['factor']
    if factor is None or not 1 < factor < n or n % factor:
        raise ArithmeticError('search did not recover a proper divisor')
    entry = dict(lower=run['low'], upper=high, covered_span=covered, outcome=run['outcome'],
                 factor=str(factor), work=run['work'])
    if method in ('centered', 'capped'):
        entry['ranges'] = run['ranges']
    return entry, elapsed


def fresh_measurement(n, method):
    command = [sys.executable, '-m', 'experiments.growing_factorial_panel', '--measure', str(n), method]
    return json.loads(subprocess.check_output(command, cwd=ROOT, text=True))


def panel(verify=False, centered=False, final_grid=False):
    rows = []
    timings = []
    rss = []
    if final_grid:
        seeds, policies = CAPPED_SEEDS, ('folded', 'capped')
    elif centered:
        seeds, policies = CENTERED_SEEDS, ('folded', 'centered')
    else:
        seeds, policies = SEEDS, METHODS
    for draw, n, generated_pair in sample(seeds):
        index = len(rows) % len(policies)
        order = policies[index:] + policies[:index]
        methods, times, peaks = {}, {}, {}
        for method in order:
            if centered or final_grid:
                methods[method], times[method], peaks[method] = fresh_measurement(n, method)
            else:
                methods[method], times[method] = evaluate(n, method)
        for run in methods.values():
            factor = int(run['factor'])
            recovered = sorted((factor,n//factor))
            if recovered != generated_pair:
                raise ArithmeticError('discovery differs from the independently drawn labels')
        if verify:
            folder = ROOT/'build/growing-factorial-panel-proofs'
            folder.mkdir(parents=True, exist_ok=True)
            path = folder/f'{n}.lean'
            path.write_text(render_certificate(n, recovered, certificate_trial_limit=1<<20))
            verify_file(path)
        timings.append(times)
        rss.append(peaks)
        rows.append(dict(draw=draw, n=str(n), bits=n.bit_length(), factors=list(map(str,recovered)),
                         order=list(order), methods=methods))
        print(n.bit_length(), draw, 'convolution input coefficients',
              {k:v['work'].get('convolution_input_coefficients',0) for k,v in methods.items()},
              'CPU seconds', {k:round(v/1e9,3) for k,v in times.items()}, flush=True)
    result = dict(seeds={str(k):v.decode() for k,v in seeds.items()},
                sample='First eight 80-bit and first 88-bit full-width products of distinct independently drawn equal-width primes.',
                wheel=WHEEL, max_span=None, rows=rows, process_cpu_ns=timings)
    if centered or final_grid:
        result['peak_process_rss_bytes'] = rss
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--write', action='store_true')
    action.add_argument('--check', action='store_true')
    action.add_argument('--measure', nargs=2, metavar=('N','METHOD'),
                        help='measure one folded, centered or capped search in this process')
    parser.add_argument('--verify', action='store_true')
    protocol = parser.add_mutually_exclusive_group()
    protocol.add_argument('--centered', action='store_true')
    protocol.add_argument('--final-grid', action='store_true')
    args = parser.parse_args()
    if args.measure:
        from resource import RUSAGE_SELF, getrusage
        n, method = args.measure
        if method not in ('centered', 'folded', 'capped'):
            parser.error('unknown single-search measurement')
        data, elapsed = evaluate(int(n), method)
        peak = getrusage(RUSAGE_SELF).ru_maxrss
        print(json.dumps([data, elapsed, peak if sys.platform == 'darwin' else peak*1024]))
        raise SystemExit(0)
    filename = CAPPED_REPORT if args.final_grid else CENTERED_REPORT if args.centered else REPORT
    report = panel(args.verify, args.centered, args.final_grid)
    if args.write:
        filename.write_text(json.dumps(report, indent=2)+'\n')
    else:
        expected = json.loads(filename.read_text())
        for field in ('process_cpu_ns', 'peak_process_rss_bytes'):
            report.pop(field, None)
            expected.pop(field, None)
        if report != expected:
            raise SystemExit('deterministic factorial-panel results differ')
