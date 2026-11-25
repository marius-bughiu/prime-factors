"""Replay the near-sum search on distinct public 2,048-bit inputs from the frozen pre-feature fixtures.

Run with ``python3 -m experiments.near_smooth_census``. Only the case identifier
and literal n are read from each record. The default emits a deterministic JSON
digest; timing and progress messages go to standard error.
"""

import argparse
from concurrent.futures import ProcessPoolExecutor
import json
from math import gcd
from pathlib import Path
import subprocess
import sys
from time import perf_counter

from .near_smooth_sum import search
from scripts.factor import render_certificate, verify_file


SNAPSHOT = '519db5f5f37c6ce1a2947de94dc03361acf8b45c'
REPO = Path(__file__).resolve().parents[1]
TOLERANCE = 2**400


def git_output(*args):
    return subprocess.check_output(['git', *args], cwd=REPO, text=True)


def snapshot_inputs():
    files = git_output('ls-tree', '-r', '--name-only', SNAPSHOT, 'benchmarks').splitlines()
    grouped = {}
    for path in files:
        if not path.endswith('.json'):
            continue
        for index, record in enumerate(json.loads(git_output('show', f'{SNAPSHOT}:{path}'))):
            literal = record.get('n')
            if not isinstance(literal, (str, int)) or not str(literal).isdigit():
                continue
            n = int(literal)
            if n.bit_length() == 2048 and gcd(n, 6) == 1:
                grouped.setdefault(n, []).append((record.get('id'), path, index))
    inputs = []
    for n, aliases in grouped.items():
        # Prefer a real case ID; break ties by fixture path and zero-based row.
        name, path, index = min(aliases, key=lambda a: (a[0] is None, a[0] or '', a[1], a[2]))
        inputs.append((name or f'{path}#{index}', path, index, len(aliases), n))
    return sorted(inputs)


def inspect_case(case):
    case_id, path, index, aliases, n = case
    start = perf_counter()
    result = search(n, TOLERANCE)
    work = result['work']
    factor = result['factor']
    row = dict(id=case_id, source=path, row=index, fixture_occurrences=aliases,
               centers=result['viable_windows'], tried=result['windows_checked'],
               remaining=result['windows_remaining'], unresolved=result['unresolved_windows'],
               quartics=work['quartic_windows'], sextics=work['sextic_windows'],
               traces=work['trace_windows'], singletons=work['singleton_tests'],
               lll_calls=work['lll_calls'], modular_exclusions=work['modular_exclusions'],
               short_polynomials=work['short_windows'], integer_root_nodes=work['integer_root_nodes'],
               factor=str(factor) if factor is not None else None,
               sum_error=str(result['sum_error']) if factor is not None else None)
    print(f"{case_id}: {row['tried']}/{row['centers']} centers, {len(row['unresolved'])} unresolved, "
          f"split={factor is not None}, {perf_counter()-start:.2f} s", file=sys.stderr, flush=True)
    return row


def report(rows):
    totals = dict(inputs=len(rows), fixture_occurrences=sum(r['fixture_occurrences'] for r in rows),
                  centers=sum(r['centers'] for r in rows), tried=sum(r['tried'] for r in rows),
                  remaining=sum(r['remaining'] for r in rows),
                  unresolved=sum(len(r['unresolved']) for r in rows),
                  lll_calls=sum(r['lll_calls'] for r in rows),
                  modular_exclusions=sum(r['modular_exclusions'] for r in rows),
                  splits=sum(r['factor'] is not None for r in rows),
                  off_center_splits=sum(r['sum_error'] not in (None, '0') for r in rows))
    return dict(snapshot=SNAPSHOT, tolerance=str(TOLERANCE), totals=totals, results=rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, choices=(1, 2), default=1)
    parser.add_argument('--proof-dir', type=Path, help='write and kernel-check a certificate for every split')
    options = parser.parse_args()
    inputs = snapshot_inputs()
    if len(inputs) != 16:
        raise ArithmeticError('historical 2,048-bit panel changed')
    if options.workers == 1:
        rows = list(map(inspect_case, inputs))
    else:
        with ProcessPoolExecutor(max_workers=options.workers) as pool:
            rows = list(pool.map(inspect_case, inputs))
    if options.proof_dir is not None:
        options.proof_dir.mkdir(parents=True, exist_ok=True)
        for (_, _, _, _, n), row in zip(inputs, rows):
            if row['factor'] is not None:
                d = int(row['factor'])
                proof = options.proof_dir / (row['id'] + '.lean')
                proof.write_text(render_certificate(n, sorted((d, n//d))))
                verify_file(proof)
    print(json.dumps(report(rows), indent=2))


if __name__ == '__main__':
    main()
