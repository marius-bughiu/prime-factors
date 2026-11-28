"""Compare product-only sum orders on complete populations of 2–14-bit prime factors."""

import json
from functools import cmp_to_key
from itertools import combinations
from math import isqrt

from experiments.grouped_offset_sweep import is_prime
from experiments.toy_period_sum_order import ALLOWED
from experiments.toy_residue_order_cost import first_square


# In each square-unit product class the discriminant vanishes modulo 5
# precisely at these two sum residues.
FAVORED = {1: {2, 3}, 4: {1, 4}}
ORDERS = ('ascending', 'global', 'weighted', 'offset')


def merge_keys(preferred, ordinary):
    """Ascending merge of two streams of (integer priority, sum); smaller sum breaks ties."""
    i = j = comparisons = 0
    sums = []
    while i < len(preferred) and j < len(ordinary):
        comparisons += 1
        if preferred[i] <= ordinary[j]:
            sums.append(preferred[i][1])
            i += 1
        else:
            sums.append(ordinary[j][1])
            j += 1
    sums.extend(s for _, s in preferred[i:])
    sums.extend(s for _, s in ordinary[j:])
    return sums, comparisons


def replay(n, bits):
    """Build orders from the public product and width and run each to its first square."""
    if not 2 <= bits <= 14 or n.bit_length() != 2*bits:
        raise ValueError('expected a full-width toy product, with 2 to 14 bits per factor')
    lower = 1 << (bits-1)
    upper = 2*lower - 1
    lo = isqrt(4*n - 1) + 1
    hi = min(lower + n//lower, upper + n//upper)
    aligned = range(lo + (n+1-lo) % 4, hi+1, 4)
    allowed = ALLOWED[n % 25]
    ascending = [s for s in aligned if s % 25 in allowed]
    classes = FAVORED.get(n % 5)
    sort_comparisons = merge_comparisons = offset_comparisons = 0
    if classes is None:
        # Scores have equal numerator here and D=s²−4n increases with s.
        global_order = weighted = offset = ascending
    else:
        records = []
        favored_keys, ordinary_keys = [], []
        favored_offsets, ordinary_offsets = [], []
        for s in ascending:
            d = s*s - 4*n
            favored = s % 5 in classes
            records.append((d, 25 if favored else 4, s))
            scale = 4 if favored else 25
            (favored_keys if favored else ordinary_keys).append((scale*d, s))
            (favored_offsets if favored else ordinary_offsets).append((scale*(s-lo), s))

        def compare(a, b):
            # Descending w/sqrt(D) is ascending D/w². A zero discriminant ranks first.
            nonlocal sort_comparisons
            sort_comparisons += 1
            left, right = a[0]*b[1], b[0]*a[1]
            if left != right:
                return -1 if left < right else 1
            return (a[2] > b[2]) - (a[2] < b[2])

        reference = [s for _, _, s in sorted(records, key=cmp_to_key(compare))]
        # These two streams are already ordered within their respective residue groups.
        global_order = [s for _, s in favored_keys] + [s for _, s in ordinary_keys]
        weighted, merge_comparisons = merge_keys(favored_keys, ordinary_keys)
        if weighted != reference:
            raise AssertionError('exact merge disagrees with the independent cross-product sort')
        offset, offset_comparisons = merge_keys(favored_offsets, ordinary_offsets)

    tests = {}
    factors = None
    for name, order in zip(ORDERS, (ascending, global_order, weighted, offset)):
        tests[name], found = first_square(n, order)
        if factors is not None and found != factors:
            raise AssertionError((n, name, found, factors))
        factors = found
    return {
        'n': n, 'factors': factors, 'lo': lo, 'hi': hi, 'tests': tests,
        'candidate_sums': len(ascending), 'mod25_lookups': len(aligned),
        'classifications': len(ascending) if classes is not None else 0,
        'score_discriminants': len(ascending) if classes is not None else 0,
        'sort_comparisons': sort_comparisons, 'merge_comparisons': merge_comparisons,
        'merge_comparisons_through_hit': min(merge_comparisons, tests['weighted']),
        'offset_comparisons': offset_comparisons,
        'offset_comparisons_through_hit': min(offset_comparisons, tests['offset']),
        'offset_order_changed': weighted != offset,
    }


def group_counts():
    return {
        'pairs': 0, **{name: 0 for name in ORDERS},
        'versus_ascending': {'earlier': 0, 'tied': 0, 'later': 0},
        'versus_global': {'earlier': 0, 'tied': 0, 'later': 0},
        'offset_order_changes': 0, 'offset_cost_changes': 0,
    }


def record(group, trace):
    tests = trace['tests']
    group['pairs'] += 1
    for name in ORDERS:
        group[name] += tests[name]
    for baseline in ('ascending', 'global'):
        difference = tests['weighted'] - tests[baseline]
        direction = 'earlier' if difference < 0 else 'later' if difference > 0 else 'tied'
        group['versus_' + baseline][direction] += 1
    group['offset_order_changes'] += trace['offset_order_changed']
    group['offset_cost_changes'] += tests['offset'] != tests['weighted']


def census(bits):
    if not 2 <= bits <= 14:
        raise ValueError('the toy census covers factor widths 2 through 14')
    primes = [p for p in range(1 << (bits-1), 1 << bits) if is_prime(p)]
    groups = {group: group_counts() for group in ('all', 'square_unit', 'other')}
    overhead = {name: 0 for name in (
        'candidate_sums', 'mod25_lookups', 'classifications', 'score_discriminants',
        'sort_comparisons', 'merge_comparisons', 'merge_comparisons_through_hit',
        'offset_comparisons', 'offset_comparisons_through_hit')}
    losses = {}
    for p, q in combinations(primes, 2):
        n = p*q
        if n.bit_length() != 2*bits:
            continue
        trace = replay(n, bits)
        if trace['factors'] != (p, q):
            raise AssertionError((n, (p, q), trace))
        record(groups['all'], trace)
        record(groups['square_unit' if n % 5 in FAVORED else 'other'], trace)
        for name in overhead:
            overhead[name] += trace[name]
        for baseline in ('ascending', 'global'):
            extra = trace['tests']['weighted'] - trace['tests'][baseline]
            if extra > losses.get(baseline, {}).get('extra_tests', 0):
                losses[baseline] = {
                    'extra_tests': extra, 'n': str(n), 'factors': [str(p), str(q)],
                    'lo': trace['lo'], 'hi': trace['hi'], 'tests': trace['tests'],
                }
    return {'bits': bits, 'groups': groups, 'overhead': overhead, 'worst_losses': losses}


if __name__ == '__main__':
    for width in range(2, 15):
        print(json.dumps(census(width)), flush=True)
