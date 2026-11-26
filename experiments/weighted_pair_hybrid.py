"""Compare three searches under 16 initial and at most 120 further square tests.

The hybrid first checks pairs agreeing at 2, 3, 5, 7 and 11. It spends the
remaining square-test allowance on the ordinary round-robin sequence.
Every policy stops at its first proper divisor. Use --time for CPU timings.
"""

import argparse
from collections import Counter, defaultdict
from itertools import combinations
import json
from math import gcd, isqrt
from pathlib import Path
from random import Random
from time import perf_counter_ns, process_time_ns

from experiments.pair_class_search import sign_tables
from experiments.weighted_pair_menu import verify_examples
from experiments.weighted_square_pairs import first_label
from scripts.factor import primes_through


REPO = Path(__file__).resolve().parents[1]
ODD_TABLES = sign_tables()[:4]  # 3, 5, 7, 11
SEED = 'weighted-pair-hybrid-16-v1'
POLICIES = ('ordinary', 'pairs', 'hybrid')
SIEVED = 'sieved_ordinary'


def passing_pairs(labels, work):
    """Return all locally compatible index pairs, including every zero row."""
    groups = defaultdict(list)
    zeros = []
    unit_steps = 0
    for index, (_, value) in enumerate(labels):
        if value == 0:
            zeros.append(index)
            continue
        v2 = (value & -value).bit_length()-1
        key = ((v2 % 2) << 3) | ((value >> v2) & 7)
        for prime, squares in ODD_TABLES:
            unit = value
            parity = 0
            residue = unit % prime
            while residue == 0:
                unit //= prime
                unit_steps += 1
                parity ^= 1
                residue = unit % prime
            key = (key << 2) | (parity << 1) | int(residue in squares)
        groups[key].append(index)
    work['keys'] += len(labels)-len(zeros)
    work['odd_mod8_checks'] += len(labels)-len(zeros)
    work['odd_unit_divisions'] += unit_steps
    work['odd_remainders'] += len(ODD_TABLES)*(len(labels)-len(zeros)) + unit_steps
    pairs = [pair for group in groups.values() for pair in combinations(group, 2)]
    if zeros:
        zero_set = set(zeros)
        pairs.extend((i, j) for i, j in combinations(range(len(labels)), 2)
                     if i in zero_set or j in zero_set)
    pairs.sort()
    work['compatible_pairs'] += len(pairs)
    return pairs


def single_passes(value, work):
    """Compare one value's local square classes with those of 1, stopping at first failure."""
    work['screened_single_labels'] += 1
    if value == 0:
        return True
    work['keys'] += 1
    v2 = (value & -value).bit_length()-1
    if v2 % 2:
        return False
    work['odd_mod8_checks'] += 1
    if (value >> v2) & 7 != 1:
        return False
    for prime, squares in ODD_TABLES:
        unit = value
        parity = 0
        residue = unit % prime
        work['odd_remainders'] += 1
        while residue == 0:
            unit //= prime
            work['odd_unit_divisions'] += 1
            parity ^= 1
            residue = unit % prime
            work['odd_remainders'] += 1
        if parity or residue not in squares:
            return False
    return True


def run(n, policy):
    if n <= 1 or gcd(n, 6) != 1 or policy not in (*POLICIES, SIEVED):
        raise ValueError('expected a positive input coprime to six and a named policy')
    work = dict(setup_gcds=9, label_sqrts=8, label_remainders=8, initial_tests=0,
                pair_tests=0, extra_single_tests=0,
                gcds_after_squares=0, keys=0, odd_unit_divisions=0, odd_remainders=0,
                odd_mod8_checks=0, compatible_pairs=0, screened_single_labels=0)
    rows = [(first_label(n, w), 4*w*n) for w in range(1, 9)]
    bits = dict(pair=0, extra_single=0)

    def finish(arm=None, divisor=None, allowance=None):
        return dict(arm=arm, divisor=divisor, ordinary_allowance=allowance, work=work,
                    max_operand_bits=bits)

    labels = []
    for (start, step), scaled in rows:
        for a in (start, start+step):
            d = a*a-scaled
            labels.append((a, d))
            root = isqrt(d)
            work['initial_tests'] += 1
            if root*root == d:
                work['gcds_after_squares'] += 1
                factor = gcd(a-root, n)
                if 1 < factor < n:
                    return finish('initial', factor)

    allowance = 120
    if policy in ('pairs', 'hybrid'):
        if policy == 'pairs':
            pairs = combinations(range(16), 2)
            allowance = 0
        else:
            pairs = passing_pairs(labels, work)
            allowance -= len(pairs)
        largest = 0
        for i, j in pairs:
            a, d = labels[i]
            b, e = labels[j]
            product = d*e
            largest = max(largest, product)
            root = isqrt(product)
            work['pair_tests'] += 1
            if root*root == product:
                work['gcds_after_squares'] += 1
                factor = gcd(a*b-root, n)
                if 1 < factor < n:
                    bits['pair'] = largest.bit_length()
                    return finish('pair', factor, allowance)
        bits['pair'] = largest.bit_length()

    largest = 0
    for rank in range(4096 if policy == SIEVED else allowance):
        if work['extra_single_tests'] == allowance:
            break
        index, row = divmod(rank, 8)
        (start, step), scaled = rows[row]
        a = start + (index+2)*step
        d = a*a-scaled
        if policy == SIEVED and not single_passes(d, work):
            continue
        largest = max(largest, d)
        root = isqrt(d)
        work['extra_single_tests'] += 1
        if root*root == d:
            work['gcds_after_squares'] += 1
            factor = gcd(a-root, n)
            if 1 < factor < n:
                bits['extra_single'] = largest.bit_length()
                return finish('extra_single', factor, allowance)
    bits['extra_single'] = largest.bit_length()
    return finish(allowance=allowance)


def population(bits):
    x = 1 << (bits-1)
    primes = [p for p in primes_through(2*x-1) if p >= x]
    return (p*q for p, q in combinations(primes, 2) if p*q >= 2*x*x)


def holdout(size=8192):
    rng = Random(SEED)
    primes = [p for p in primes_through(65535) if p >= (1 << 15)]
    found = {}
    attempts = 0
    while len(found) < size:
        p, q = rng.choice(primes), rng.choice(primes)
        attempts += 1
        if p != q and p*q >= 1 << 31:
            found[p*q] = None
    return list(found), attempts


def compare_inputs(inputs, strong=False):
    policies = (*POLICIES, SIEVED) if strong else POLICIES
    counts = Counter(dict.fromkeys((*policies,'eligible','initial','hybrid_pair_hits',
        'pair_hits_also_ordinary','pair_hits_inside_retained_ordinary_prefix',
        'only_hybrid','only_ordinary'), 0))
    if strong:
        counts.update(dict.fromkeys(('only_hybrid_vs_sieved','only_sieved_vs_hybrid',
                                     'sieved_cap_exhausted','sieved_root_budget_exhausted'), 0))
    work = {policy: Counter() for policy in policies}
    max_bits = {policy: Counter() for policy in policies}
    examples = {}
    for n in inputs:
        runs = {policy: run(n, policy) for policy in policies}
        counts['eligible'] += 1
        for policy, result in runs.items():
            work[policy].update(result['work'])
            max_bits[policy] |= Counter(result['max_operand_bits'])
            if result['divisor'] is not None:
                f = result['divisor']
                if not (1 < f < n and n % f == 0):
                    raise ArithmeticError('invalid factor returned')
                counts[policy] += 1
        ordinary, hybrid = runs['ordinary'], runs['hybrid']
        if ordinary['arm'] == 'initial':
            counts['initial'] += 1
            continue
        if strong:
            sieved = runs[SIEVED]
            if not sieved['divisor']:
                if sieved['work']['extra_single_tests'] == 120:
                    counts['sieved_root_budget_exhausted'] += 1
                else:
                    counts['sieved_cap_exhausted'] += 1
            if bool(sieved['divisor']) != bool(hybrid['divisor']):
                name = 'only_hybrid_vs_sieved' if hybrid['divisor'] else 'only_sieved_vs_hybrid'
                counts[name] += 1
                if name not in examples:
                    examples[name] = dict(n=str(n), divisor=str(hybrid['divisor'] or sieved['divisor']))
        if hybrid['arm'] == 'pair':
            counts['hybrid_pair_hits'] += 1
            if ordinary['divisor'] is not None:
                counts['pair_hits_also_ordinary'] += 1
                if ordinary['work']['extra_single_tests'] <= hybrid['ordinary_allowance']:
                    counts['pair_hits_inside_retained_ordinary_prefix'] += 1
        if bool(hybrid['divisor']) != bool(ordinary['divisor']):
            name = 'only_hybrid' if hybrid['divisor'] is not None else 'only_ordinary'
            counts[name] += 1
            if name not in examples:
                result = hybrid if hybrid['divisor'] else ordinary
                examples[name] = dict(n=str(n), divisor=str(result['divisor']),
                                      hybrid_ordinary_allowance=hybrid['ordinary_allowance'],
                                      ordinary_checks=ordinary['work']['extra_single_tests'])
    return dict(counts=dict(counts), work=work, max_operand_bits=max_bits, first_examples=examples)


def report():
    fresh, attempts = holdout()
    cases = json.loads((REPO / 'benchmarks/factor-sum-quantile.json').read_text())
    return dict(reproduce='python3 -m experiments.weighted_pair_hybrid',
                filter='v2 parity and odd unit mod 8, then v_p parity and unit square class '
                       'at 3, 5, 7 and 11. Positive nonzero excesses.',
                common='Eight weighted label square roots. First two labels on each row; '
                       'stop on first proper gcd. Thereafter, up to 120 additional square tests.',
                ordinary_order='For each label index 2 through 16, visit weights 1 through 8.',
                sieved_baseline='Panel and blind holdout also apply the same small-prime square '
                                'tests to singles, stopping after a split, 120 exact extra roots '
                                'or 4,096 additional labels.',
                exhaustive={str(b): compare_inputs(population(b)) for b in (10, 12, 14)},
                holdout=dict(seed=SEED, draws=attempts, size=len(fresh), **compare_inputs(fresh, True)),
                panel=[dict(id=row['id'], n=row['n'], **compare_inputs([int(row['n'])], True))
                       for row in cases])


def timings():
    inputs, _ = holdout(1024)
    cases = json.loads((REPO / 'benchmarks/factor-sum-quantile.json').read_text())
    panels = [ ('14-bit-side-full', list(population(14)), 1), ('16-bit-side', inputs, 1),
               ('80-bit', [int(r['n']) for r in cases[:8]], 64),
               ('2048-bit', [int(r['n']) for r in cases[8:]], 32) ]
    rows = []
    for name, numbers, repeats in panels:
        for policy in (*POLICIES, SIEVED):
            beginning = process_time_ns()
            wall = perf_counter_ns()
            successes = sum(run(n, policy)['divisor'] is not None
                            for _ in range(repeats) for n in numbers)
            rows.append(dict(panel=name, inputs=len(numbers), repeats=repeats, policy=policy,
                             splits_including_repetitions=successes, cpu_ns=process_time_ns()-beginning,
                             wall_ns=perf_counter_ns()-wall))
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--time', action='store_true', help='measure end-to-end CPU and wall time')
    group.add_argument('--verify-examples', action='store_true', help='also kernel-check sample splits')
    args = parser.parse_args()
    result = timings() if args.time else report()
    if args.verify_examples:
        verify_examples(hit for group in (*result['exhaustive'].values(), result['holdout'], *result['panel'])
                        for hit in group['first_examples'].values())
    print(json.dumps(result, indent=2))
