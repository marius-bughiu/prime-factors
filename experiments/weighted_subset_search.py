"""Find the shortest factor-producing subset of sixteen public weighted rows."""

import argparse
from collections import Counter
import cProfile
import json
from math import gcd, isqrt, prod
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.pell_relations import _dependencies, _private_parts
from experiments.weighted_pair_hybrid import SEED, holdout, population, single_passes
from experiments.weighted_square_pairs import first_label
from scripts.factor import render_certificate, verify_file


def search(n):
    """Use ranks 0 and 1 of weights 1..8. Inspect integer square products only."""
    if n <= 32 or gcd(n, 6) != 1:
        raise ValueError('expected n above 32 and coprime to six')
    rows = []
    for weight in range(1, 9):
        first, stride = first_label(n, weight)
        for rank in range(2):
            label = first + rank*stride
            rows.append((weight, rank, label, label**2 - 4*weight*n))
    total = 2**len(rows)-1
    work = dict(rows=len(rows), label_gcds=0, pruning_rounds=0,
                private_square_tests=0, rows_removed=0, basis_rows=0,
                dimension=None, square_subsets=None, relation_square_tests=0,
                relation_gcds=0, covered_subsets=0, remaining_subsets=total)
    for weight, rank, label, excess in rows:
        work['label_gcds'] += 1
        divisor = gcd(label, n)
        if 1 < divisor < n:
            return dict(factor=divisor, outcome='label_gcd', minimum_rows=None,
                        witness=dict(rows=[[weight, rank]], labels=[str(label)]), work=work)
        if excess == 0:
            # A²=4wn implies a nonunit. If n|A, then n|4w≤32 as well.
            raise ArithmeticError('zero remainder without a proper label gcd')

    while rows:
        private = _private_parts([row[3] for row in rows])
        work['private_square_tests'] += len(rows)
        kept = [row for row, value in zip(rows, private) if isqrt(value)**2 == value]
        if len(kept) == len(rows):
            break
        work['pruning_rounds'] += 1
        work['rows_removed'] += len(rows)-len(kept)
        rows = kept
    work['basis_rows'] = len(rows)
    basis = _dependencies([row[3] for row in rows])
    masks = [0]
    for v in basis:
        masks += [mask ^ v for mask in masks]
    work.update(dimension=len(basis), square_subsets=len(masks)-1)
    witness = None
    factor = None
    for mask in sorted(masks[1:], key=lambda m: (bin(m).count('1'), m)):
        selected = [row for j, row in enumerate(rows) if mask & (1 << j)]
        value = prod(row[3] for row in selected)
        root = isqrt(value)
        work['relation_square_tests'] += 1
        if root**2 != value:
            raise ArithmeticError('coprime basis reported a nonsquare')
        labels = prod(row[2] for row in selected)
        minus, plus = gcd(labels-root, n), gcd(labels+root, n)
        work['relation_gcds'] += 2
        if witness is None and (1 < minus < n or 1 < plus < n):
            factor = minus if 1 < minus < n else plus
            witness = dict(rows=[[w, j] for w, j, _, _ in selected],
                           labels=[str(a) for _, _, a, _ in selected],
                           excesses=[str(d) for _, _, _, d in selected],
                           square_root=str(root), minus_gcd=str(minus), plus_gcd=str(plus))
    work.update(covered_subsets=total, remaining_subsets=0)
    return dict(factor=factor, outcome='relation' if witness else 'no_split',
                minimum_rows=len(witness['rows']) if witness else None,
                witness=witness, work=work)


def ordinary(n, max_tests, *, sieve=False):
    """Check ordinary single labels in increasing rank, then increasing weight."""
    starts = [first_label(n, w) for w in range(1, 9)]
    work = Counter()
    tests = labels = 0
    for number in range(4096 if sieve else max_tests):
        if tests == max_tests:
            break
        rank, i = divmod(number, 8)
        first, step = starts[i]
        a = first+step*rank
        value = a*a-4*(i+1)*n
        labels += 1
        if sieve and not single_passes(value, work):
            continue
        tests += 1
        y = isqrt(value)
        if y*y == value:
            for divisor in (gcd(a-y, n), gcd(a+y, n)):
                if 1 < divisor < n:
                    return dict(factor=divisor, tests=tests, labels=labels,
                                weight=i+1, rank=rank, screen=dict(work))
    return dict(factor=None, tests=tests, labels=labels, screen=dict(work))


def operations(function, *args, **kwargs):
    """Count actual Python calls to both math primitives, including reused helpers."""
    profile = cProfile.Profile()
    result = profile.runcall(function, *args, **kwargs)
    stats = {entry.code: entry.callcount for entry in profile.getstats()
             if isinstance(entry.code, str)}
    return result, {name: stats.get(f'<built-in method math.{name}>', 0)
                    for name in ('isqrt', 'gcd')}


def relation_certificate(n, result):
    """Prove both primalities and both signed gcds using the actual public rows."""
    factor = result['factor']
    factors = sorted((factor, n//factor))
    source = render_certificate(n, factors)
    if result['outcome'] != 'relation':
        return source, 'PrimeFactors.Generated.factorization'
    witness = result['witness']
    rows = witness['rows']
    terms = [f'(WeightedMultiplierLabels.labelAt {n} {w} {j})' for w, j in rows]
    checks = []
    for index, ((w, _), term, label) in enumerate(zip(rows, terms, witness['labels'])):
        floor = isqrt(4*w*n-1)
        checks.append(f"""private theorem label{index} : {term} = {label} := by
  exact certified_label (k:={floor+1})
    (ceil_from_squares (k:={floor}) (by decide +kernel) (by decide +kernel))
    (by decide +kernel)
""")
    root = witness['square_root']
    excess_product = ' * '.join(f'({a}^2 - 4*{w}*{n})' for a, (w, _) in zip(terms, rows))
    labels = ' * '.join(terms)
    statement = f"""namespace PrimeFactors.Generated

private theorem ceil_from_squares {{m k : ℕ}} (lo : k^2 < m) (hi : m ≤ (k+1)^2) :
    ceilSqrt m = k+1 := by
  apply le_antisymm (ceilSqrt_le_iff.mpr hi)
  have neg : ¬ ceilSqrt m ≤ k := fun h => (not_le_of_gt lo) (ceilSqrt_le_iff.mp h)
  omega

private theorem certified_label {{n w i a k : ℕ}} (floor : ceilSqrt (4*w*n) = k)
    (aligned : let s := Nat.gcd 24 (2*(w+n)); k+((w+n)%s+s-k%s)%s+s*i = a) :
    WeightedMultiplierLabels.labelAt n w i = a := by
  unfold WeightedMultiplierLabels.labelAt
  rw [floor]
  exact aligned

{chr(10).join(checks)}
theorem subsetFactorization : ExactFactorization {n} {factors} ∧
    {excess_product} = {root}^2 ∧
    Nat.gcd ({labels} - {root}) {n} = {witness['minus_gcd']} ∧
    Nat.gcd ({labels} + {root}) {n} = {witness['plus_gcd']} := by
  refine ⟨factorization, ?_⟩
  rw [{', '.join(f'label{i}' for i in range(len(rows)))}]
  decide +kernel

#print axioms subsetFactorization
end PrimeFactors.Generated
"""
    return ('import PrimeFactors.WeightedMultiplierLabels\n' + source + '\n' + statement,
            'PrimeFactors.Generated.subsetFactorization')


def verify_hit(n, result):
    source, name = relation_certificate(n, result)
    with TemporaryDirectory() as directory:
        proof = Path(directory)/'WeightedSubset.lean'
        proof.write_text(source)
        verify_file(proof, theorem_name=name)


def census(inputs):
    counts = Counter()
    examples = []
    for n in inputs:
        result = search(n)
        counts['inputs'] += 1
        counts[result['outcome']] += 1
        size = result['minimum_rows']
        if size is not None:
            counts[f'minimum_{size}'] += 1
        if size is None or size < 4:
            continue
        _, subset_ops = operations(search, n)
        first, single_ops = operations(ordinary, n, 65535)
        # Both searches first spend eight square roots generating identical label origins.
        matched, matched_ops = operations(ordinary, n, subset_ops['isqrt']-8)
        sieved, sieved_ops = operations(ordinary, n, subset_ops['isqrt']-8, sieve=True)
        examples.append(dict(n=str(n), ordinal=counts['inputs'], divisor=str(result['factor']),
                             search=result, subset_operations=subset_ops, first_ordinary=first,
                             first_ordinary_operations=single_ops, matched_ordinary=matched,
                             matched_ordinary_operations=matched_ops, sieved_ordinary=sieved,
                             sieved_ordinary_operations=sieved_ops))
    return dict(counts=dict(counts), long_only=examples)


def report():
    inputs, draws = holdout()
    path = Path(__file__).resolve().parents[1]/'benchmarks/factor-sum-quantile.json'
    panel = [dict(id=item['id'], n=item['n'], **search(int(item['n'])))
             for item in json.loads(path.read_text())]
    return dict(reproduce='python3 -m experiments.weighted_subset_search --verify-examples',
                protocol='After checking label gcds, remove rows with nonsquare private parts. '
                         'Refine the remaining integers into coprime bases. Enumerate every '
                         'nonzero parity-kernel vector, check its square and both gcd signs. '
                         'Keep the shortest splitting subset, breaking ties by mask.',
                cohorts='All eligible distinct equal-width prime pairs with full-width product '
                        'at the named bit sizes, in weighted_pair_hybrid.population order. '
                        'The 16-bit panel reuses its published sampling seed and ordered draw list. '
                        'The search sees only the product. The ten fixed controls supply id and n.',
                baseline='Ordinary search checks weights 1..8 round-robin starting at rank zero, '
                         'up to 65,535 labels. The matched run caps integer square-root calls at '
                         'the measured subset total, including the eight shared setup roots. '
                         'A further matched run screens by 2,3,5,7,11 before each root and '
                         'caps visits at 4,096 labels. Operand lengths, gcd refinement, '
                         'screening and parity elimination costs differ.',
                exhaustive={str(bits): census(population(bits)) for bits in (11, 12, 14)},
                holdout=dict(bits=16, seed=SEED, draws=draws, **census(inputs)), panel=panel)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int, nargs='?')
    parser.add_argument('--verify-examples', action='store_true')
    args = parser.parse_args()
    if args.n is not None:
        result = search(args.n)
        if args.verify_examples and result['factor']:
            verify_hit(args.n, result)
    else:
        result = report()
        if args.verify_examples:
            for cohort in (*result['exhaustive'].values(), result['holdout']):
                for example in cohort['long_only']:
                    verify_hit(int(example['n']), example['search'])
    print(json.dumps(result, indent=2))
