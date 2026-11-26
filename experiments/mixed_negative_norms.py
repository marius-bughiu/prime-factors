"""Count and check matches of N-t² and 2N-s² on positive unit labels.

Run python3 -m experiments.mixed_negative_norms [--verify-examples]. The small
census uses exact squarefree kernels. The independent bounded search receives
only the product and window width and tests every pair by integer square root.
"""
import argparse
from collections import Counter, defaultdict
from itertools import combinations, product
import json
from math import gcd, isqrt
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.gap_coverage import primes_through

REPO = Path(__file__).resolve().parents[1]
COUNTS = (
    'products', 'label_gcds', 'unit_labels_1', 'unit_labels_2', 'mixed_pairs', 'mixed_matches', 'mixed_splits', 'mixed_trivial',
    'mixed_equal_matches', 'mixed_equal_splits', 'mixed_unequal_matches', 'mixed_unequal_splits',
    'mixed_unequal_trivial', 'mixed_unequal_match_products', 'mixed_unequal_split_products',
    'mixed_unequal_large_class', 'mixed_unequal_large_class_small_kernel', 'mixed_large_class', 'mixed_large_class_small_kernel', 'mixed_match_products',
    'mixed_split_products', 'mixed_large_class_products', 'single_pairs',
    'single_matches', 'single_splits', 'single_trivial', 'single_match_products',
    'single_split_products', 'both_split_products', 'mixed_only_split_products',
    'single_only_split_products', 'neither_split_products', 'unequal_and_single_split_products',
    'unequal_only_split_products', 'single_only_vs_unequal_products', 'neither_unequal_nor_single_products',
)


def squarefree_kernels(limit):
    """Remove p² once on every multiple of p², again on every multiple of p⁴, etc."""
    kernels = list(range(limit+1))
    for p in primes_through(isqrt(limit)):
        square = p*p
        step = square
        while step <= limit:
            for n in range(step, limit+1, step):
                kernels[n] //= square
            step *= square
    return kernels


def match_witness(n, t, s, d, e, root):
    """Use the largest shared coefficient; neither input needs to be factored."""
    g = gcd(d, e)
    a, b = isqrt(d//g), isqrt(e//g)
    if (g*a*a, g*b*b, g*a*b) != (d, e, root):
        raise ArithmeticError('square match did not yield the two integral representations')
    minus, plus = gcd(t*s-root, n), gcd(t*s+root, n)
    if (g > 2 or n % 8 == 7) and not 1 < minus < n:
        raise ArithmeticError('unit match contradicted the mixed-norm splitting criterion')
    witness = {key: str(value) for key, value in dict(t=t, s=s, d=d, e=e, g=g, a=a, b=b,
                                                       root=root, gcd_minus=minus, gcd_plus=plus).items()}
    if not 1 < minus < n:
        sign = 1 if minus == n else -1
        j, r1 = divmod(t*s-sign*root, n)
        v, r2 = divmod(t*sign*b+s*a, n)
        if r1 or r2 or j*j+g*v*v != 2:
            raise ArithmeticError('trivial match lacks the required representation of 2')
        witness['trivial_quotient'] = dict(sign=sign, j=str(j), v=str(v))
    return witness


def search(n, width=32):
    """Scan the last `width` positive labels strictly below each square-root endpoint."""
    if n <= 1 or n % 2 == 0 or width < 0:
        raise ValueError('expected an odd product above one and a nonnegative label budget')
    work = dict(endpoint_roots=2, labels=[0, 0], unit_labels=[0, 0], label_gcds=0,
                proper_label_gcds=0, square_tests=0, max_square_test_bits=0, matches=0,
                splits=0, trivial=0, equal_matches=0, unequal_matches=0, unequal_splits=0, large_class_matches=0, match_common_gcds=0,
                representation_roots=0, match_result_gcds=0)
    direct = first = split = unequal = None
    unit_rows = []
    for weight in (1, 2):
        highest = isqrt(weight*n-1)
        kept = []
        for x in range(highest, max(0, highest-width), -1):
            work['labels'][weight-1] += 1
            work['label_gcds'] += 1
            divisor = gcd(x, n)
            if divisor == 1:
                kept.append((x, weight*n-x*x))
            elif divisor < n:
                work['proper_label_gcds'] += 1
                if direct is None:
                    direct = dict(weight=weight, label=str(x), divisor=str(divisor))
        work['unit_labels'][weight-1] = len(kept)
        unit_rows.append(kept)
    for (t, d), (s, e) in product(*unit_rows):
        candidate = d*e
        root = isqrt(candidate)
        work['square_tests'] += 1
        work['max_square_test_bits'] = max(work['max_square_test_bits'], candidate.bit_length())
        if root*root != candidate:
            continue
        witness = match_witness(n, t, s, d, e, root)
        work['matches'] += 1
        work['equal_matches' if d == e else 'unequal_matches'] += 1
        work['match_common_gcds'] += 1
        work['representation_roots'] += 2
        work['match_result_gcds'] += 2
        work['large_class_matches'] += int(int(witness['g']) > 2)
        if first is None:
            first = witness
        if 1 < int(witness['gcd_minus']) < n:
            work['splits'] += 1
            if d != e:
                work['unequal_splits'] += 1
                if unequal is None:
                    unequal = witness
            if split is None:
                split = witness
        else:
            work['trivial'] += 1
    # Keep both discoveries visible even if checking a label already found a factor.
    if direct is not None:
        factor, source = int(direct['divisor']), 'label_gcd'
    elif split is not None:
        factor, source = int(split['gcd_minus']), 'mixed_match'
    else:
        factor, source = None, None
    return dict(factor=factor, factor_source=source, direct_hit=direct, first_match=first,
                split_witness=split, unequal_witness=unequal, work=work)


def full_counts(n, kernels):
    """Census every positive unit label. Input primality and factor labels are unnecessary."""
    groups = []
    for weight in (1, 2):
        by_kernel = defaultdict(list)
        for x in range(1, isqrt(weight*n-1)+1):
            if gcd(n, x) == 1:
                d = weight*n-x*x
                by_kernel[kernels[d]].append((x, d))
        groups.append(by_kernel)
    left, right = groups
    nl, nr = (sum(map(len, group.values())) for group in groups)
    counts = dict.fromkeys(COUNTS, 0)
    counts.update(products=1, label_gcds=isqrt(n-1)+isqrt(2*n-1), unit_labels_1=nl, unit_labels_2=nr,
                  mixed_pairs=nl*nr, single_pairs=nl*(nl-1)//2)
    examples = {}
    for kernel, rows in left.items():
        for (t, d), (s, e) in product(rows, right.get(kernel, ())):
            root = isqrt(d*e)
            witness = match_witness(n, t, s, d, e, root)
            proper = 1 < int(witness['gcd_minus']) < n
            g = int(witness['g'])
            counts['mixed_matches'] += 1
            counts['mixed_splits' if proper else 'mixed_trivial'] += 1
            counts['mixed_large_class'] += int(g > 2)
            counts['mixed_large_class_small_kernel'] += int(g > 2 and kernel <= 2)
            case = dict(n=str(n), kernel=str(kernel), **witness)
            if d == e:
                counts['mixed_equal_matches'] += 1
                counts['mixed_equal_splits'] += int(proper)
            else:
                counts['mixed_unequal_matches'] += 1
                counts['mixed_unequal_splits' if proper else 'mixed_unequal_trivial'] += 1
                counts['mixed_unequal_large_class'] += int(g > 2)
                if g > 2 and kernel <= 2:
                    counts['mixed_unequal_large_class_small_kernel'] += 1
                    examples.setdefault('extra_certificate_from_gcd', case)
                if proper and n % 8 == 7:
                    examples.setdefault('unequal_split_seven', case)
                if not proper:
                    examples.setdefault('unequal_trivial', case)
            if g > 2 and (not examples.get('largest_common_class') or g > int(examples['largest_common_class']['g'])):
                examples['largest_common_class'] = case
            if d != e and g > 2 and (not examples.get('largest_unequal_class') or g > int(examples['largest_unequal_class']['g'])):
                examples['largest_unequal_class'] = case
        for (t, d), (s, e) in combinations(rows, 2):
            root = isqrt(d*e)
            if root*root != d*e:
                raise ArithmeticError('kernel mismatch in weight-one comparison')
            proper = 1 < gcd(n, t*s-root) < n
            counts['single_matches'] += 1
            counts['single_splits' if proper else 'single_trivial'] += 1
    for counter, result in (('mixed_match_products', 'mixed_matches'), ('mixed_split_products', 'mixed_splits'),
                            ('mixed_large_class_products', 'mixed_large_class'), ('single_match_products', 'single_matches'),
                            ('single_split_products', 'single_splits'), ('mixed_unequal_match_products', 'mixed_unequal_matches'),
                            ('mixed_unequal_split_products', 'mixed_unequal_splits')):
        counts[counter] = int(bool(counts[result]))
    if counts['mixed_splits']:
        overlap = 'both_split_products' if counts['single_splits'] else 'mixed_only_split_products'
    else:
        overlap = 'single_only_split_products' if counts['single_splits'] else 'neither_split_products'
    counts[overlap] = 1
    if counts['mixed_unequal_splits']:
        unequal_overlap = 'unequal_and_single_split_products' if counts['single_splits'] else 'unequal_only_split_products'
    else:
        unequal_overlap = 'single_only_vs_unequal_products' if counts['single_splits'] else 'neither_unequal_nor_single_products'
    counts[unequal_overlap] = 1
    return counts, examples


def census(bits):
    floor = 1 << (bits-1)
    primes = [p for p in primes_through(2*floor-1) if p >= floor]
    kernels = squarefree_kernels(2*(2*floor-1)**2)
    residues = {str(r): Counter() for r in (1, 3, 5, 7)}
    total = Counter()
    examples = {}
    for p, q in combinations(primes, 2):
        n = p*q
        if n < 2*floor**2:
            continue
        counts, local = full_counts(n, kernels)
        residues[str(n % 8)].update(counts)
        total.update(counts)
        if counts['mixed_equal_splits'] != 1 or counts['mixed_equal_matches'] != 1:
            raise ArithmeticError('expected exactly the equal-norm Fermat pair in this population')
        if not counts['mixed_unequal_matches']:
            local['no_unequal_match'] = dict(n=str(n))
        if not counts['mixed_unequal_splits']:
            local['no_unequal_split'] = dict(n=str(n))
        for key, example in local.items():
            result = int(example.get('gcd_minus', 1))
            if result not in (1, n, p, q):
                raise ArithmeticError('discovered divisor fails independent label check')
            old = examples.get(key)
            if key.startswith('largest'):
                take = old is None or (int(example['g']), -n) > (int(old['g']), -int(old['n']))
            else:
                take = old is None or n < int(old['n'])
            if take:
                examples[key] = example
    return dict(factor_bits=bits, by_mod8=residues, total=total, examples=examples)


def witness_lean(n, witness):
    """Strict standalone Lean certificate for a square match and its two gcds."""
    n = int(n)
    w = {k: int(witness[k]) for k in ('t', 's', 'd', 'e', 'g', 'a', 'b', 'root', 'gcd_minus', 'gcd_plus')}
    t, s, d, e, g, a, b, z, minus, plus = w.values()
    arithmetic = f'''import PrimeFactors.MixedNegativeNorms

namespace PrimeFactors.Generated.MixedNegative

def MatchArithmetic : Prop :=
    {t}^2+{d}={n} ∧ {s}^2+{e}=2*{n} ∧ Nat.Coprime {t} {n} ∧ Nat.Coprime {s} {n} ∧
    Nat.gcd {d} {e}={g} ∧ {d}={g}*{a}^2 ∧ {e}={g}*{b}^2 ∧ {d}*{e}={z}^2 ∧
    (Int.natAbs (({t}:ℤ)*{s}-{z})).gcd {n}={minus} ∧ ({t}*{s}+{z}).gcd {n}={plus}

theorem exactMatch : MatchArithmetic := by
  unfold MatchArithmetic
  decide +kernel
'''
    if n % 8 == 7 or g > 2:
        # Check the theorem's hypotheses on the emitted representations, in addition to the direct gcds.
        parameters = f'(N:={n}) (d:={g}) (t:={t}) (s:={s}) (a:={a}) (b:={b})'
        if n % 8 == 7:
            proof = f'exact MixedNegativeNorms.split_two_seven {parameters} (by decide) (by decide) (by decide) (by decide) (by decide)'
        else:
            proof = (f'apply MixedNegativeNorms.split {parameters} (k:=1) (l:=2) (by decide) (by decide) (by decide)\n'
                     '  exact MixedNegativeNorms.large_class (by decide) (by decide)')
        arithmetic += f'''
def Criterion : Prop :=
    let x : ZMod {n} := (({t}:ℤ)*{s} : ℤ)
    let y : ZMod {n} := (({g}:ℤ)*{a}*{b} : ℤ)
    1 < (x-y).val.gcd {n} ∧ (x-y).val.gcd {n} < {n}

theorem witness : MatchArithmetic ∧ Criterion := by
  refine ⟨exactMatch, ?_⟩
  {proof}
'''
    elif 'trivial_quotient' in witness:
        q = witness['trivial_quotient']
        sign, j, v = (int(q[k]) for k in ('sign', 'j', 'v'))
        arithmetic += f'''
theorem witness : MatchArithmetic ∧ (({j}:ℤ)^2+{g}*({v})^2=2 ∧
    ({t}:ℤ)*{s}-({sign})*{z}={n}*({j}) ∧ ({t}:ℤ)*({sign})*{b}+{s}*{a}={n}*({v})) :=
  ⟨exactMatch, by decide +kernel⟩
'''
    else:
        arithmetic += '\ntheorem witness : MatchArithmetic := exactMatch\n'
    return arithmetic+'\n#print axioms witness\nend PrimeFactors.Generated.MixedNegative\n'



def report():
    small = [census(bits) for bits in (6, 7, 8)]
    controls = json.loads((REPO/'benchmarks/factor-sum-quantile.json').read_text())
    inputs = [('mixed-negative-43423', 43423)]
    for row in controls:
        if row['id'] in ('quantile-fresh-2048', 'quantile-crossed-2048'):
            inputs.append((row['id'].replace('quantile', 'mixed-negative'), int(row['n'])))
    if len(inputs) != 3:
        raise ValueError('expected both registered 2048-bit controls')
    return dict(factor_interval='2^(b-1) <= p < q < 2^b; p*q >= 2^(2*b-1)',
                labels='positive unit labels with t^2<N and s^2<2N; equal magnitudes counted separately',
                census_method='mixed_pairs and single_pairs count potential pairs; squarefree kernels index the unit labels, so only matching pairs enter the square and gcd checks',
                bounded_width=32,
                example_selection='43423 is the first eligible 8-bit N = 7 mod 8 in ascending product order with an unequal bounded split and no direct label gcd (21st product tested).',
                exhaustive=small, bounded=[dict(id=cid, n=str(n), **search(n)) for cid, n in inputs])


def verify_examples(data):
    from scripts.factor import verify_file
    examples = [(r['n'], r['split_witness']) for r in data['bounded'] if r['split_witness']]
    examples.extend((w['n'], w) for batch in data['exhaustive'] for w in batch['examples'].values() if 'g' in w)
    with TemporaryDirectory() as temp:
        for i, (n, w) in enumerate(examples):
            path = Path(temp)/f'MixedNegative{i}.lean'
            path.write_text(witness_lean(n, w))
            verify_file(path, 'PrimeFactors.Generated.MixedNegative.witness')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-examples', action='store_true')
    args = parser.parse_args()
    result = report()
    if args.verify_examples:
        verify_examples(result)
    print(json.dumps(result, indent=2))
