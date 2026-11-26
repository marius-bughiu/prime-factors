"""Compare three readouts on the same cubic square candidates."""

import argparse
from collections import Counter
import json
from math import gcd
from pathlib import Path
from tempfile import TemporaryDirectory

from .cubic_square_readout import direct_readout, projected_readout
from .cubic_trace_search import (
    POINTS, character_places, character_word, check_subset, collect, kernels,
    primes_through, select_polynomial,
)

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE = ROOT / 'research/cubic-readout-panel.json'


def properly_splits(n, pairs):
    return any(1 < g < n for pair in pairs for g in pair)


def compare(n, *, cap=128):
    work = Counter()
    selected = select_polynomial(n, work)
    if selected is None:
        return {'n': n, 'status': 'no polynomial'}
    m, f, _ = selected
    c, b, a = f
    disc = a*a*b*b-4*b**3-4*a**3*c-27*c*c+18*a*b*c
    if gcd(disc, n) != 1:
        return {'n': n, 'status': 'excluded ramified input'}
    rows = collect(m, f, POINTS, work)
    places = character_places(f, work)
    basis = kernels(rows, [character_word(row, places, work) for row in rows], 8)
    size = min(cap, 2**len(basis)-1)
    counts, first, rescued, mask = Counter(), {}, None, 0
    factors = set()
    for i in range(1, size+1):
        mask ^= basis[(i & -i).bit_length()-1]
        ordinary, wit = check_subset(n, m, f, rows, mask)
        beta, z = tuple(map(int, wit['beta'])), int(wit['rational_root'])
        if gcd(z, n) != 1:
            counts['nonunit_rational_root'] += 1
            continue
        projected = projected_readout(n, m, f, beta, z)
        counts['projected_root_nodes'] += projected['work'].get('integer_root_nodes', 0)
        counts['original_root_nodes'] += ordinary['work']['integer_root_nodes']
        actual = ordinary['witnesses']
        if bool(actual) != bool(projected['signed_traces']):
            raise ArithmeticError('projecting by a nonzero field element changed square status')
        if not actual:
            counts['nonsquare'] += 1
            continue
        counts['square'] += 1
        direct = [direct_readout(n, m, f, beta, z, w) for w in actual]
        if any(d['denominator_gcd'] != 1 for d in direct):
            raise ArithmeticError('nonunit primitive denominator at a good prime')
        pairs = {'ordinary': [p['gcds'] for p in ordinary['probes']],
                 'direct': [d['gcds'] for d in direct], 'projected': projected['gcds']}
        # Global root sign can exchange the two gcds.
        if {tuple(sorted(v)) for v in pairs['direct']} != {tuple(sorted(v)) for v in pairs['projected']}:
            raise ArithmeticError('direct and projected gcds disagree at an unramified unit')
        split = {key: properly_splits(n, values) for key, values in pairs.items()}
        for key, success in split.items():
            counts[key+'_splits'] += int(success)
            if success:
                first.setdefault(key, i)
        for values in pairs.values():
            factors.update(g for pair in values for g in pair if 1 < g < n)
        if split['ordinary'] and not split['direct']:
            counts['ordinary_only'] += 1
        if split['direct'] and not split['ordinary']:
            counts['direct_only'] += 1
            if rescued is None:
                rescued = {'index': i, 'rows': wit['rows'], 'beta': wit['beta'], 'z': str(z),
                           'ordinary': pairs['ordinary'], 'direct': direct, 'projected': projected}
    return {'n': n, 'status': 'tested', 'm': m, 'f': list(f), 'tested': size,
            'counts': dict(counts), 'first': first, 'factors': sorted(factors), 'first_rescue': rescued}


def panel():
    # A bounded retrospective census containing the products in the exploratory scan.
    # The factor-search function receives only n. Both prime labels remain here.
    primes = [p for p in primes_through(83) if p >= 17]
    cases = []
    for i, p in enumerate(primes):
        for q in primes[i+1:]:
            if q > 2*p:
                break
            case = compare(p*q)
            if case.get('factors') and case['factors'] != [p, q]:
                raise ArithmeticError('reported divisors disagree with sample labels')
            cases.append(case)
    return {'min_prime': 17, 'max_prime': 83, 'partner_ratio_max': 2,
            'row_count': len(POINTS), 'character_bits': 8, 'dependency_cap': 128, 'cases': cases}


def verify(data):
    from scripts.factor import render_certificate, verify_file
    with TemporaryDirectory() as folder:
        path = Path(folder)/'CubicReadout.lean'
        count = 0
        for row in data['cases']:
            factors = row.get('factors')
            if factors:
                path.write_text(render_certificate(row['n'], factors))
                verify_file(path)
                count += 1
    return count


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    data = panel()
    if args.check:
        if json.loads(ARCHIVE.read_text()) != data:
            raise SystemExit('cubic readout panel differs')
        print(f"Checked all {len(data['cases'])} census inputs.")
    if args.verify:
        print(f'Kernel-checked {verify(data)} distinct factorizations.')
    if not args.check and not args.verify:
        print(json.dumps(data, indent=2))
