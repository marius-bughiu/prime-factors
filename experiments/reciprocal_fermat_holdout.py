"""Compare complete Fermat searches with reusable sum tables on independent prime pairs."""

import argparse
from bisect import bisect_left
from hashlib import sha256
from itertools import permutations
import json
from math import gcd, isqrt
from pathlib import Path
import platform
from statistics import median
from time import perf_counter_ns, process_time_ns

from experiments.affine_radix_holdout import draw_prime
from experiments.reciprocal_anchor import find_anchor, oriented
from scripts.factor import render_certificate, verify_file


ROOT = Path(__file__).resolve().parents[1]
SEED = b'reciprocal-fermat-holdout-v1'
METHODS = ('wheel60', 'ordinary', 'oriented')
ORDERS = tuple(permutations(METHODS))
BUDGET = 256
MAX_TABLE_PERIOD = 1_000_000
WHEEL = 60


def inputs(bits):
    seed = SEED + b'/' + str(bits).encode('ascii')
    pairs = []
    sample = 0
    while len(pairs) < 12:
        pair = sorted(draw_prime(side, sample, bits=bits, seed=seed) for side in (b'p', b'q'))
        if pair[0] != pair[1]:
            pairs.append((sample, pair))
        sample += 1
    return pairs


def bounds(n, bits):
    # The smaller factor x lies above both lower bounds. x+n/x decreases up to sqrt(n).
    max_factor = (1 << bits) - 1
    smallest = max(1 << (bits-1), (n+max_factor-1)//max_factor)
    return isqrt(4*n-1)+1, smallest + n//smallest


def ordinary_classes(n, d):
    squares = bytearray(d)
    for i in range(d//2+1):
        squares[i*i % d] = 1
    c = 4*n % d
    return [s for s in range(d) if squares[(s*s-c) % d]]


def first_split(n, lo, hi, period, rows):
    """Stream the sorted period, starting directly at the first row at or above lo."""
    base, offset = divmod(lo, period)
    base *= period
    start = bisect_left(rows, offset)
    tests = 0
    while base <= hi:
        for index in range(start, len(rows)):
            s = base + rows[index]
            if s > hi:
                return None, tests
            delta = s*s-4*n
            gap = isqrt(delta)
            tests += 1
            if gap*gap == delta and (s-gap) % 2 == 0:
                p, q = (s-gap)//2, (s+gap)//2
                if p > 1 and p*q == n:
                    return [str(p), str(q)], tests
        base += period
        start = 0
    return None, tests


def search(n, bits, method):
    """Only the public product, its two factor widths and the method enter this function."""
    begin = process_time_ns()
    lo, hi = bounds(n, bits)
    wheel = {(x+n*pow(x, -1, WHEEL)) % WHEEL for x in range(WHEEL) if gcd(x, WHEEL) == 1}
    count = dict(wheel_rows=len(wheel), cf_steps=0, cf_replay=0, table_root_entries=0,
                 table_sum_tests=0, ordinary_classes=0, tag_queries=0, crt_pairs=0,
                 sorted_entries=0, discriminant_isqrts=0)
    public = dict(interval=[lo, hi], outcome='wheel' if method == 'wheel60' else 'no_anchor')
    ticks = dict(anchor=0, table=0, orientation=0, crt_sort=0, scan=0)
    ready = process_time_ns()
    ticks['wheel_and_bounds'] = ready-begin
    classes = None
    period = WHEEL
    if method != 'wheel60':
        anchor = find_anchor(n, BUDGET, WHEEL)
        end = process_time_ns()
        ticks['anchor'] = end-ready
        count['cf_steps'] = BUDGET
        if anchor and 'setup_factor' in anchor:
            f = anchor['setup_factor']
            if not 1 < f < n or n % f:
                raise ArithmeticError('continued fraction returned invalid factor')
            pair = [str(x) for x in sorted((f, n//f))]
            count['cf_steps'] = anchor['step']
            public.update(outcome='setup_gcd', anchor=anchor)
            return dict(pair=pair, **public, counts=count), ticks
        if anchor:
            public['anchor'] = anchor
            count['cf_replay'] = anchor['step']
            d, e = anchor['period'], anchor['root']
            if d <= MAX_TABLE_PERIOD:
                start = process_time_ns()
                local = ordinary_classes(n, d)
                ticks['table'] = process_time_ns()-start
                count.update(table_root_entries=d//2+1, table_sum_tests=d, ordinary_classes=len(local))
                if method == 'oriented':
                    start = process_time_ns()
                    # Since zero is absent, the sorted lower half represents the ± pairs.
                    if not local or local[0] == 0 or len(local) % 2 or local[len(local)//2-1] > d//2:
                        raise ArithmeticError('expected opposite nonzero residues')
                    local = [s if oriented(s, d, e) else d-s for s in local[:len(local)//2]]
                    ticks['orientation'] = process_time_ns()-start
                    count['tag_queries'] = len(local)
                start = process_time_ns()
                inverse = pow(WHEEL, -1, d)
                classes = sorted(w + WHEEL*((s-w)*inverse % d) for w in wheel for s in local)
                period = WHEEL*d
                ticks['crt_sort'] = process_time_ns()-start
                count['crt_pairs'] = len(classes)
                public['outcome'] = 'table'
            else:
                public['outcome'] = 'oversize_anchor'
    if classes is None:
        start = process_time_ns()
        classes = sorted(wheel)
        ticks['crt_sort'] = process_time_ns()-start
    count['sorted_entries'] = len(classes)
    start = process_time_ns()
    pair, count['discriminant_isqrts'] = first_split(n, lo, hi, period, classes)
    ticks['scan'] = process_time_ns()-start
    return dict(pair=pair, **public, counts=count), ticks


def certificate(rows):
    """Combine normal repository factor certificates under separate namespaces and audit one theorem."""
    imports, bodies, cases, proofs = set(), [], [], []
    namespace = 'PrimeFactors.ReciprocalFermatHoldout'
    for i, row in enumerate(rows):
        n = int(row['n'])
        recovered = row['methods']['oriented']['pair']
        if any(row['methods'][m]['pair'] != recovered for m in METHODS):
            raise ArithmeticError(f'the methods disagree on {n}')
        pair = [int(x) for x in recovered]
        source = render_certificate(n, pair)
        imports.update(line for line in source.splitlines() if line.startswith('import '))
        body = source.split('namespace PrimeFactors.Generated\n', 1)[1].split('#print axioms', 1)[0].strip()
        bodies.append(f'namespace Case{i}\n{body}\nend Case{i}')
        cases.append(f'ExactFactorization {n} {pair}')
        proofs.append(f'Case{i}.factorization')
    parts = ['\n'.join(sorted(imports)), 'set_option exponentiation.threshold 256',
             'set_option maxRecDepth 8192', f'namespace {namespace}', *bodies,
             'theorem panel :\n    ' + ' ∧\n    '.join(cases) + ' :=\n  ⟨' + ', '.join(proofs) + '⟩',
             '#print axioms panel', f'end {namespace}', '']
    path = ROOT / 'build' / 'ReciprocalFermatHoldout.lean'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text('\n\n'.join(parts))
    verify_file(path, namespace+'.panel')
    return dict(theorem=namespace+'.panel', checked_rows=len(rows),
                sha256=sha256(path.read_bytes()).hexdigest())


def timing_summary(rows):
    result = {}
    for method in METHODS:
        sums = {phase: [sum(row['timings_cpu_ns'][method][rep][phase] for row in rows)
                        for rep in range(len(ORDERS))]
                for phase in rows[0]['timings_cpu_ns'][method][0]}
        count = {key: sum(row['methods'][method]['counts'][key] for row in rows)
                 for key in rows[0]['methods'][method]['counts']}
        wall = [sum(row['timings_wall_ns'][method][rep] for row in rows) for rep in range(len(ORDERS))]
        result[method] = dict(counts=count, complete_batch_cpu_ns=sums['total'], complete_batch_wall_ns=wall,
                              median_batch_phase_cpu_ns={k: int(median(v)) for k, v in sums.items()})
    return result


def panel():
    rows, expected = [], []
    for bits in (20, 24):
        for sample, pair in inputs(bits):
            rows.append(dict(bits=bits, sample=sample, n=str(pair[0]*pair[1]), methods={},
                             timings_cpu_ns={m: [] for m in METHODS},
                             timings_wall_ns={m: [] for m in METHODS}))
            expected.append([str(x) for x in pair])
    for repetition in range(len(ORDERS)):
        for i, row in enumerate(rows):
            for method in ORDERS[(repetition+i) % len(ORDERS)]:
                n, bits = int(row['n']), row['bits']
                wall_start = perf_counter_ns()
                cpu_start = process_time_ns()
                result, ticks = search(n, bits, method)
                ticks['total'] = process_time_ns()-cpu_start
                elapsed_wall = perf_counter_ns()-wall_start
                if result['pair'] != expected[i]:
                    raise ArithmeticError(f"split mismatch in public sample {row['bits']}/{row['sample']}")
                if repetition and result != row['methods'][method]:
                    raise ArithmeticError('timing repetitions changed deterministic search work')
                row['methods'][method] = result
                row['timings_cpu_ns'][method].append(ticks)
                row['timings_wall_ns'][method].append(elapsed_wall)
    return dict(seed=SEED.decode(), cf_budget=BUDGET, max_table_period=MAX_TABLE_PERIOD,
                repetitions=len(ORDERS), python=platform.python_version(), machine=platform.machine(),
                platform=platform.system(), timer='process_time_ns', cases=rows,
                summaries={str(bits): timing_summary([r for r in rows if r['bits'] == bits])
                           for bits in (20, 24)})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--output', type=Path, help='write a freshly timed and certified panel')
    mode.add_argument('--verify-report', type=Path, help='recheck the published splits without retiming')
    args = parser.parse_args()
    if args.verify_report:
        saved = json.loads(args.verify_report.read_text())
        if certificate(saved['cases']) != saved['certificate']:
            raise ArithmeticError('the generated certificate differs from the recorded receipt')
        print(f"Verified {len(saved['cases'])} factorizations in one Lean theorem.")
        return
    report = panel()
    report['certificate'] = certificate(report['cases'])
    content = json.dumps(report, indent=2)+'\n'
    if args.output:
        args.output.write_text(content)
    else:
        print(content, end='')


if __name__ == '__main__':
    main()
