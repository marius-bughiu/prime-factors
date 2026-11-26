"""Compare all one-, two- and three-row square tests with matched ordinary tests.

Run python3 -m experiments.weighted_square_triples --verify-examples to replay the
censuses and verify the prime factorizations highlighted in the JSON report.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from math import gcd, isqrt, prod
from pathlib import Path

from experiments.pell_relations import check_rows
from experiments.weighted_pair_hybrid import SEED, holdout, population
from experiments.weighted_pair_menu import verify_examples
from experiments.weighted_square_pairs import first_label

REPO = Path(__file__).resolve().parents[1]
ARMS = ('initial', 'pair', 'triple', 'extra_single')


def _subset_count(n, rows):
    """The nonzero products form a binary parity kernel. A zero row is handled separately."""
    nonzero = [(weight_rank, excess, label) for weight_rank, label, excess, _ in rows if excess]
    zeros = len(rows) - len(nonzero)
    work = dict(pruning_rounds=0, private_pruned=0, min_private_bits=None,
                dependencies=0, tested=0, factor=None)
    result = check_rows(n, nonzero, work)
    # Each subset using a zero row is square, for any choices of nonzero rows.
    square_subsets = (2**zeros-1) * 2**len(nonzero) + 2**result['dependencies']-1
    return dict(rows=len(rows), nonempty_subsets=2**len(rows)-1, zero_rows=zeros,
                private_pruned=result['private_pruned'], pruning_rounds=result['pruning_rounds'],
                minimum_private_bits=result['min_private_bits'],
                nonzero_kernel_dimension=result['dependencies'], basis_gcds=result['tested'],
                square_subsets=square_subsets)


def compare(n, *, all_subsets=False):
    """Read n alone. Test both gcd signs on every square, preserving the first split per arm."""
    if n <= 1 or gcd(n, 6) != 1:
        raise ValueError('expected an integer above one coprime to six')
    work = dict(setup_gcds=9, label_roots=8, label_remainders=8)
    max_bits = {}
    results = dict.fromkeys((*ARMS, 'genuine_triple'))
    for arm in ARMS:
        for suffix in ('tests', 'squares', 'minus_gcds', 'plus_gcds', 'proper_minus',
                       'proper_plus', 'splitting_tests'):
            work[f'{arm}_{suffix}'] = 0
        max_bits[arm] = 0
        max_bits[arm + '_gcd'] = 0
    max_bits['label_root'] = (32*n-1).bit_length()
    work['genuine_triple_splits'] = 0

    def record_square(arm, subset, root):
        left = prod(row[1] for row in subset)
        minus = gcd(left-root, n)
        plus = gcd(left+root, n)
        work[arm+'_squares'] += 1
        work[arm+'_minus_gcds'] += 1
        work[arm+'_plus_gcds'] += 1
        work[arm+'_proper_minus'] += int(1 < minus < n)
        work[arm+'_proper_plus'] += int(1 < plus < n)
        max_bits[arm+'_gcd'] = max(max_bits[arm+'_gcd'], n.bit_length(),
                                   (left+root).bit_length(), abs(left-root).bit_length())
        if not (1 < minus < n or 1 < plus < n):
            return
        work[arm+'_splitting_tests'] += 1
        genuine = arm == 'triple' and all(not row[3] for row in subset)
        work['genuine_triple_splits'] += int(genuine)
        if results[arm] is not None and (not genuine or results['genuine_triple'] is not None):
            return
        factor, sign = (minus, 'minus') if 1 < minus < n else (plus, 'plus')
        hit = dict(rows=[list(row[0]) for row in subset], labels=[str(row[1]) for row in subset],
                   excesses=[str(row[2]) for row in subset], square_root=str(root),
                   sign=sign, divisor=str(factor))
        if results[arm] is None:
            results[arm] = hit
        if genuine and results['genuine_triple'] is None:
            results['genuine_triple'] = hit

    rows = []
    for weight in range(1, 9):
        first, step = first_label(n, weight)
        target = 4*weight*n
        for rank in range(72):
            label = first+rank*step
            excess = label*label-target
            root = isqrt(excess)
            square = root*root == excess
            arm = 'initial' if rank < 2 else 'extra_single'
            if rank < 2 or square:
                row = ((weight, rank), label, excess, square)
                if rank < 2:
                    rows.append(row)
                if square:
                    record_square(arm, (row,), root)
            # The excess grows with rank at each fixed weight.
            if rank in (1, 71):
                max_bits[arm] = max(max_bits[arm], excess.bit_length())
    work['initial_tests'], work['extra_single_tests'] = 16, 560

    largest = sorted((row[2] for row in rows), reverse=True)
    max_bits['pair'] = (largest[0]*largest[1]).bit_length()
    max_bits['triple'] = (largest[0]*largest[1]*largest[2]).bit_length()
    for i, j in combinations(range(len(rows)), 2):
        pair = rows[i][2]*rows[j][2]
        root = isqrt(pair)
        work['pair_tests'] += 1
        if root*root == pair:
            record_square('pair', (rows[i], rows[j]), root)
        for k in range(j+1, len(rows)):
            triple = pair*rows[k][2]
            root = isqrt(triple)
            work['triple_tests'] += 1
            if root*root == triple:
                record_square('triple', (rows[i], rows[j], rows[k]), root)
    if all_subsets:
        results['subsets'] = _subset_count(n, rows)
    return dict(**results, work=work, max_operand_bits=max_bits)


def summarize(inputs):
    counts = Counter(dict.fromkeys(('eligible', *ARMS, 'genuine_triple', 'baseline',
                                   'triple_added', 'genuine_added', 'extra_added',
                                   'genuine_and_extra_added', 'genuine_only', 'extra_only'), 0))
    overlap, totals, max_bits = Counter(), Counter(), Counter()
    examples = {}
    for n in inputs:
        result = compare(n)
        totals.update(result['work'])
        max_bits |= Counter(result['max_operand_bits'])
        counts['eligible'] += 1
        for arm in (*ARMS, 'genuine_triple'):
            counts[arm] += int(result[arm] is not None)
        arms = [arm for arm in ARMS if result[arm] is not None]
        overlap[' + '.join(arms) or 'none'] += 1
        if result['initial'] or result['pair']:
            counts['baseline'] += 1
            continue
        triple, genuine, ordinary = (result[k] for k in ('triple', 'genuine_triple', 'extra_single'))
        counts['triple_added'] += int(bool(triple))
        counts['genuine_added'] += int(bool(genuine))
        counts['extra_added'] += int(bool(ordinary))
        counts['genuine_and_extra_added'] += int(bool(genuine and ordinary))
        counts['genuine_only'] += int(bool(genuine and not ordinary))
        counts['extra_only'] += int(bool(ordinary and not triple))
        for key, hit in (('genuine_and_extra_added', genuine if ordinary else None),
                         ('genuine_only', genuine if not ordinary else None),
                         ('extra_only', ordinary if not triple else None)):
            if hit and key not in examples:
                examples[key] = dict(n=str(n), **hit)
    return dict(counts=dict(counts), overlap=dict(sorted(overlap.items())),
                work=dict(totals), max_operand_bits={k: max_bits[k] for k in ('label_root', *ARMS,
                    *(arm+'_gcd' for arm in ARMS))}, first_examples=examples)


def report():
    cases = json.loads((REPO/'benchmarks/factor-sum-quantile.json').read_text())
    panel = [dict(id=case['id'], n=case['n'],
                  **compare(int(case['n']), all_subsets=int(case['n']).bit_length() == 2048))
             for case in cases]
    inputs, draws = holdout()
    return dict(reproduce='python3 -m experiments.weighted_square_triples --verify-examples',
                setup='Weights 1..8. Use ranks 0..1 in singles, pairs and triples, then ranks '
                      '2..71 at each weight for the 560 matched ordinary tests. Try both gcd signs '
                      'on every square. All arms finish.',
                counting='Genuine means all three component excesses are nonsquares. Added means '
                         'the initial singles and pairs both miss. Genuine only also requires the '
                         '560 ordinary additions to miss. Overlap records every successful arm.',
                sources='The two exhaustive samples use every distinct sorted equal-width prime '
                        'pair with a full-width product. Holdout reuses weighted_pair_hybrid.holdout. '
                        'Panel reads only the ten IDs and public products from factor-sum-quantile.json.',
                exhaustive={str(bits): summarize(population(bits)) for bits in (11, 12)},
                holdout=dict(factor_bits=16, seed=SEED, draws=draws, **summarize(inputs)),
                panel=panel, pilot=dict(n='2100271', **compare(2100271)))


def highlighted(result):
    for group in (*result['exhaustive'].values(), result['holdout']):
        yield from group['first_examples'].values()
    for case in (*result['panel'], result['pilot']):
        for name in (*ARMS, 'genuine_triple'):
            if case[name]:
                yield dict(n=case['n'], **case[name])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-examples', action='store_true')
    args = parser.parse_args()
    result = report()
    if args.verify_examples:
        verify_examples(highlighted(result))
    print(json.dumps(result, indent=2))
