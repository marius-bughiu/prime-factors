"""Direct square-test census on complete, bounded populations of small prime pairs."""

import json
from dataclasses import asdict
from itertools import combinations
from math import isqrt

from experiments.grouped_offset_sweep import is_prime
from experiments.toy_period_sum_order import ALLOWED
from experiments.toy_residue_order_cost import Counts, first_square


def census(bits):
    """Uniform p<q, both b-bit, with 2b-bit product and square unit product mod 5."""
    if not 2 <= bits <= 14:
        raise ValueError('the toy census covers factor widths 2 through 14')
    lower = 1 << (bits - 1)
    upper = 2 * lower - 1
    primes = [p for p in range(lower, upper + 1) if is_prime(p)]
    counts = {name: Counts() for name in ('pooled', 'equal', 'opposite')}
    full_width = 0
    residue_lookups = 0
    examples = {}
    for p, q in combinations(primes, 2):
        n = p * q
        if n.bit_length() != 2 * bits:
            continue
        full_width += 1
        if n % 5 not in (1, 4):
            continue

        # The common width and product determine both orders before either test.
        lo = isqrt(4 * n - 1) + 1
        hi = min(lower + n // lower, upper + n // upper)
        first = lo + (n + 1 - lo) % 4
        aligned = range(first, hi + 1, 4)
        allowed_sums = ALLOWED[n % 25]
        ascending = [s for s in aligned if s % 25 in allowed_sums]
        prioritized = sorted(ascending, key=lambda s: (s * s - 4 * n) % 5 != 0)
        base_cost, base_factors = first_square(n, ascending)
        priority_cost, priority_factors = first_square(n, prioritized)
        if base_factors != (p, q) or priority_factors != (p, q):
            raise AssertionError((n, base_factors, priority_factors, (p, q)))

        if p % 5 == q % 5:
            branch = 'equal'
            if priority_cost > base_cost:
                raise AssertionError(('favored target cost more', n))
        elif (p + q) % 5 == 0:
            branch = 'opposite'
            if priority_cost < base_cost:
                raise AssertionError(('ordinary target cost less', n))
        else:
            raise AssertionError(('square product outside both branches', n))
        counts[branch].record(base_cost, priority_cost, len(ascending))
        counts['pooled'].record(base_cost, priority_cost, len(ascending))
        residue_lookups += len(aligned)
        # Retain one reproducible example per direction at a single width.
        if bits == 12 and base_cost != priority_cost and branch not in examples:
            examples[branch] = {
                'n': str(n), 'factors': [str(p), str(q)],
                'lo': lo, 'hi': hi, 'ascending_tests': base_cost,
                'prioritized_tests': priority_cost, 'mod25_lookups': len(aligned),
                'priority_classifications': len(ascending),
            }
    groups = {}
    for name, count in counts.items():
        groups[name] = {
            **asdict(count),
            'pairs': count.earlier + count.tied + count.later,
            'saved_tests': count.ascending_tests - count.prioritized_tests,
        }
    result = {
        'bits': bits, 'primes': len(primes), 'full_width_pairs': full_width,
        'groups': groups, 'mod25_lookups': residue_lookups,
    }
    if examples:
        result['examples'] = examples
    return result


if __name__ == '__main__':
    for width in range(2, 15):
        print(json.dumps(census(width)), flush=True)
