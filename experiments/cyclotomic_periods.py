"""Replay product-derived exponents using the Lean geometric period tables."""

import json
import subprocess
import sys
from math import gcd
from pathlib import Path
from time import perf_counter_ns


ROOT = Path(__file__).resolve().parents[1]


def reduced_table_search(n, base, stride):
    proc = subprocess.run(['lake', 'env', 'lean', '--run', 'experiments/ReducedOrders.lean',
                           'search', str(n), str(base), str(stride)], cwd=ROOT, capture_output=True,
                          text=True, timeout=900)
    if proc.returncode:
        raise RuntimeError(f'Lean table search failed: {proc.stderr}\n{proc.stdout}')
    return json.loads(proc.stdout)


def search(n, base, degree, stride):
    """The Lean tables raise the supplied base to n-1 internally."""
    if n <= 1 or degree < 1 or stride < 1:
        raise ValueError('expected n > 1 and positive degree and stride')
    start = perf_counter_ns()
    initial_gcd = gcd(base, n)
    if initial_gcd > 1:
        proper = initial_gcd < n
        return dict(factor=str(initial_gcd) if proper else None,
                    outcome='base gcd' if proper else 'base divisible by product',
                    entries_per_table=0, giants_probed=0, batch_gcds=0, halving_gcds=0,
                    table_search_nanoseconds=0, search_nanoseconds=perf_counter_ns() - start)
    e = n**degree - 1
    effective_base = pow(base, e // (n - 1), n)
    preconditioning_ns = perf_counter_ns() - start
    result = reduced_table_search(n, effective_base, stride)
    table_ns = result['search_nanoseconds']
    start = perf_counter_ns()
    result['halving_gcds'] = 0
    if result['outcome'] == 'identity base':
        two_part = e & -e
        value = pow(base, e // two_part, n)
        for _ in range(two_part.bit_length() - 1):
            if value == 1:
                break
            factor = gcd(value - 1, n)
            result['halving_gcds'] += 1
            if 1 < factor < n:
                result.update(factor=str(factor), outcome='identity split by halving')
                break
            value = value * value % n
    result['table_search_nanoseconds'] = table_ns
    result['search_nanoseconds'] = preconditioning_ns + table_ns + perf_counter_ns() - start
    return result


def expand_cases(groups):
    """Each degree has its own table budget, outcome, and verification receipt."""
    for group in groups:
        for trial in group['trials']:
            case = dict(trial, n=group['n'], base=group['base'], stride=group['stride'])
            case['remaining'] = [group['n']] if case['status'] == 'partial' else []
            yield case


if __name__ == '__main__':
    sys.path.insert(0, str(ROOT))
    from scripts.benchmark import run_case

    proofs = ROOT / 'build' / 'cyclotomic-proofs'
    proofs.mkdir(parents=True, exist_ok=True)
    groups = json.loads((ROOT / 'benchmarks/cyclotomic-periods.json').read_text())
    for fixture in expand_cases(groups):
        result = run_case(fixture, 'cyclotomic', proofs)
        print(json.dumps(result), flush=True)
