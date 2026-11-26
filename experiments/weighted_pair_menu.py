"""Compare a fixed menu of cross-row square tests with an equal number of single tests.

The 16 initial labels use weights 1 through 8. All 120 unordered pairs are
tested, as are the next 15 single labels at each weight. No arm stops early.
Reproduce the archived counts with python3 -m experiments.weighted_pair_menu.
"""

import argparse
import json
from itertools import combinations
from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.weighted_square_pairs import first_label
from scripts.factor import primes_through, render_certificate, verify_file


REPO = Path(__file__).resolve().parents[1]


def compare(n):
    """Discover proper divisors from n alone. Charge a gcd on every square."""
    if n <= 1 or gcd(n, 6) != 1:
        raise ValueError('expected an integer above one coprime to six')
    labels = []
    single = [None, None]
    single_gcds = [0, 0]
    largest_single = 0
    for w in range(1, 9):
        label, stride = first_label(n, w)
        scaled = 4*w*n
        for index in range(17):
            excess = label*label-scaled
            root = isqrt(excess)
            square = root*root == excess
            arm = int(index >= 2)
            if not arm:
                labels.append((w, index, label, excess, square))
            if square:
                single_gcds[arm] += 1
                divisor = gcd(n, label-root)
                if 1 < divisor < n and single[arm] is None:
                    single[arm] = str(divisor)
            if index == 16:
                largest_single = max(largest_single, excess)
            label += stride

    pair_gcds = proper = 0
    first_pair = first_nonsquare = first_cross = None
    for one, two in combinations(labels, 2):
        w, i, a, d, single_d = one
        v, j, b, e, single_e = two
        product = d*e
        root = isqrt(product)
        if root*root != product:
            continue
        pair_gcds += 1
        divisor = gcd(n, a*b-root)
        if 1 < divisor < n:
            proper += 1
            hit = dict(rows=[[w, i], [v, j]], labels=[str(a), str(b)], excesses=[str(d), str(e)],
                       square_root=str(root), divisor=str(divisor))
            if first_pair is None:
                first_pair = hit
            if not single_d and not single_e:
                if first_nonsquare is None:
                    first_nonsquare = hit
                if w != v and first_cross is None:
                    first_cross = hit
    two_largest = sorted(row[3] for row in labels)[-2:]
    return dict(initial=single[0], extra_single=single[1], pair=first_pair,
                nonsquare_pair=first_nonsquare, cross_weight_nonsquare_pair=first_cross,
                work=dict(setup_gcds=9, label_sqrts=8, label_remainders=8, initial_tests=16,
                          pair_tests=120, extra_single_tests=120,
                          initial_gcds=single_gcds[0], pair_gcds=pair_gcds,
                          extra_single_gcds=single_gcds[1], proper_pair_gcds=proper),
                max_operand_bits=dict(pair=(two_largest[0]*two_largest[1]).bit_length(),
                                      extra_single=largest_single.bit_length()))


def census(bits):
    x = 1 << (bits-1)
    primes = [p for p in primes_through(2*x-1) if p >= x]
    counts = dict(eligible=0, initial=0, pair_added=0, nonsquare_pair_added=0,
                  cross_weight_nonsquare_pair_added=0, extra_single_added=0,
                  both_arms_added=0, pair_only=0, cross_weight_nonsquare_pair_only=0,
                  extra_single_only=0)
    examples = {}
    work = {}
    max_bits = dict(pair=0, extra_single=0)
    for p, q in combinations(primes, 2):
        n = p*q
        if n < 2*x*x:
            continue
        result = compare(n)
        for name, value in result['work'].items():
            work[name] = work.get(name, 0) + value
        for name, bits_used in result['max_operand_bits'].items():
            max_bits[name] = max(max_bits[name], bits_used)
        counts['eligible'] += 1
        pair = result['pair']
        nonsquare = result['nonsquare_pair']
        cross = result['cross_weight_nonsquare_pair']
        for divisor in (result['initial'], result['extra_single'], *(hit['divisor'] for hit in
                        (pair, nonsquare, cross) if hit)):
            if divisor is not None and int(divisor) not in (p, q):
                raise ArithmeticError('returned divisor differs from the independent count labels')
        if result['initial']:
            counts['initial'] += 1
            continue
        extra = result['extra_single'] is not None
        counts['pair_added'] += int(bool(pair))
        counts['nonsquare_pair_added'] += int(bool(nonsquare))
        counts['cross_weight_nonsquare_pair_added'] += int(bool(cross))
        counts['extra_single_added'] += int(extra)
        counts['both_arms_added'] += int(bool(pair) and extra)
        counts['pair_only'] += int(bool(pair) and not extra)
        counts['cross_weight_nonsquare_pair_only'] += int(bool(cross) and not extra)
        counts['extra_single_only'] += int(extra and not pair)
        for name, hit in [('nonsquare_pair_added', nonsquare), ('pair_only', pair if not extra else None),
                          ('cross_weight_nonsquare_pair_only', cross if not extra else None)]:
            if hit and name not in examples:
                examples[name] = dict(n=str(n), **hit)
    return dict(factor_bits=bits, counts=counts, work=work, max_operand_bits=max_bits,
                first_examples=examples)


def report():
    cases = json.loads((REPO / 'benchmarks/factor-sum-quantile.json').read_text())
    # Only public n and the case ID enter this comparison.
    panel = [dict(id=row['id'], n=row['n'], **compare(int(row['n']))) for row in cases]
    return dict(reproduce='python3 -m experiments.weighted_pair_menu',
                sample='All distinct sorted b-bit prime pairs with a full 2b-bit product. '
                       'Small census divisors are compared with sieve labels.',
                panel_source='benchmarks/factor-sum-quantile.json: first eight quantile 80-bit '
                             'draws, followed by the fresh and crossed 2048-bit controls.',
                exhaustive=[census(b) for b in (10, 12, 14)], panel=panel)


def verify_examples(hits):
    """Kernel-check the factorizations of the small examples singled out in the report."""
    seen = set()
    with TemporaryDirectory() as directory:
        for hit in hits:
            n, factor = int(hit['n']), int(hit['divisor'])
            if n in seen:
                continue
            seen.add(n)
            proof = Path(directory) / f'WeightedPair{n}.lean'
            proof.write_text(render_certificate(n, sorted((factor, n//factor))))
            verify_file(proof)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-examples', action='store_true',
                        help='also kernel-check the representative small factorizations')
    args = parser.parse_args()
    result = report()
    if args.verify_examples:
        verify_examples(hit for group in result['exhaustive'] for hit in group['first_examples'].values())
    print(json.dumps(result, indent=2))
