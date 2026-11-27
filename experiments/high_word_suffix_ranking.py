"""Rank candidate sums from a high product word and a public product remainder."""

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations
import json
from math import isqrt, lcm
from pathlib import Path

from experiments.high_word_sum_ranking import check_midpoint, gap_interval
from scripts.factor import primes_through


ROOT = Path(__file__).resolve().parents[1]
CENSUS = ROOT / 'research/high-word-suffix-ranking.json'


@lru_cache(maxsize=16)
def square_classes(modulus):
    if modulus < 1:
        raise ValueError('expected a positive modulus')
    classes = defaultdict(list)
    for gap in range(lcm(2, modulus)):
        classes[gap * gap % modulus, gap % 2].append(gap)
    return dict(classes)


def allowed_gaps(classes, modulus, residue, midpoint):
    return classes.get(((midpoint * midpoint - residue) % modulus, (midpoint + 1) % 2), ())


def propose(bits, word, modulus, residue):
    if bits < 2 or not 0 <= residue < modulus:
        raise ValueError('expected a valid factor width and remainder')
    base = 1 << bits
    if not base // 2 <= word < base:
        raise ValueError('expected a full-width product')
    lower = word * base
    upper = lower + base - 1
    floor = isqrt(upper)
    period = lcm(2, modulus)
    classes = square_classes(modulus)
    roots = 1
    class_counts = occupied = 0
    best = earliest = None
    best_count = 0
    for midpoint in range(floor, floor + period + 1):
        residues = allowed_gaps(classes, modulus, residue, midpoint)
        if not residues:
            continue
        low, high, setup = gap_interval(base, lower, upper, midpoint)
        roots += setup
        if low > high:
            continue
        class_counts += len(residues)
        support = sum((high - r) // period - (low - 1 - r) // period for r in residues)
        if support:
            occupied += 1
            if earliest is None:
                earliest = midpoint
        if support > best_count:
            best = midpoint
            best_count = support
    return dict(midpoint=best, earliest=earliest, support=best_count, occupied=occupied,
                period=period, rows=period + 1, table_entries=period, setup_roots=roots,
                residue_class_counts=class_counts,
                maximum_proved=bits >= 14 and base >= 4096 * period ** 3)


def search(n, bits, modulus):
    if bits < 2 or modulus < 1 or n < 3 or n % 2 == 0:
        raise ValueError('expected an odd product, equal factor widths and a positive modulus')
    work = propose(bits, n >> bits, modulus, n % modulus)
    factor, tests = (None, 0) if work['midpoint'] is None else check_midpoint(n, work['midpoint'])
    work['square_tests'] = tests
    return factor, work


@lru_cache(maxsize=32768)
def first_local_offset(modulus, residue, start_class):
    classes = square_classes(modulus)
    for offset in range(lcm(2, modulus)):
        if allowed_gaps(classes, modulus, residue, start_class + offset):
            return offset
    return None


def first_local_midpoint(n, modulus):
    """First ordinary Fermat midpoint compatible with the same remainder and parity."""
    start = 1 + isqrt(n - 1)
    offset = first_local_offset(modulus, n % modulus, start % lcm(2, modulus))
    return None if offset is None else start + offset


@lru_cache(maxsize=512)
def local_prefix(modulus, residue):
    classes = square_classes(modulus)
    prefix = [0]
    for midpoint in range(lcm(2, modulus)):
        prefix.append(prefix[-1] + bool(allowed_gaps(classes, modulus, residue, midpoint)))
    return tuple(prefix)


def prefix_count(stop, prefix):
    """Number of locally allowed nonnegative positions strictly below stop."""
    cycles, remainder = divmod(stop, len(prefix) - 1)
    return cycles * prefix[-1] + prefix[remainder]


def scan_fermat(n, modulus, budget):
    """Actually perform up to budget admissible square tests with the same local sieve."""
    if modulus < 1 or n < 3 or budget < 0:
        raise ValueError('expected a positive modulus, product and nonnegative budget')
    start = 1 + isqrt(n - 1)
    midpoint = start
    period = lcm(2, modulus)
    tests = 0
    while tests < budget:
        offset = first_local_offset(modulus, n % modulus, midpoint % period)
        if offset is None:
            break
        midpoint += offset
        factor, used = check_midpoint(n, midpoint)
        tests += used
        if factor is not None:
            return factor, dict(midpoint=midpoint, setup_roots=1, square_tests=tests,
                                table_entries=period, rows=midpoint-start+1)
        midpoint += 1
    return None, dict(midpoint=None, setup_roots=1, square_tests=tests,
                      table_entries=period, rows=midpoint-start)


def census(bits, modulus):
    base = 1 << bits
    primes = [p for p in primes_through(base - 1) if p >= base // 2]
    predictions = {}
    totals = Counter(pairs=0, ranked=0, earliest=0, fermat_with_remainder=0, ranked_only=0,
                     fermat_only=0, gained_vs_earliest=0, lost_vs_earliest=0, empty_block=0,
                     fermat_at_ranked_root_budget=0, ranked_only_at_equal_budget=0)
    for p, q in combinations(primes, 2):
        n = p * q
        word, residue = n // base, n % modulus
        if word < base // 2:
            continue
        key = word, residue
        if key not in predictions:
            predictions[key] = propose(bits, word, modulus, residue)
        choice = predictions[key]
        actual = (p + q) // 2
        hit = actual == choice['midpoint']
        first = actual == choice['earliest']
        baseline = actual == first_local_midpoint(n, modulus)
        start = 1 + isqrt(n - 1)
        prefix = local_prefix(modulus, residue)
        needed = prefix_count(actual + 1, prefix) - prefix_count(start, prefix)
        final_root = choice['midpoint'] is not None and choice['midpoint'] >= start
        equal_hit = needed <= choice['setup_roots'] + int(final_root) - 1
        totals.update(dict(pairs=1, ranked=hit, earliest=first, fermat_with_remainder=baseline,
                           ranked_only=hit and not baseline, fermat_only=baseline and not hit,
                           gained_vs_earliest=hit and not first, lost_vs_earliest=first and not hit,
                           empty_block=choice['midpoint'] is None, fermat_at_ranked_root_budget=equal_hit,
                           ranked_only_at_equal_budget=hit and not equal_hit))
    return dict(factor_bits=bits, modulus=modulus, occupied_readings=len(predictions), **totals)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    # 24 records the small-prime parity/stride information, 120 also keeps the residue modulo five.
    panel = [census(bits, m) for bits in (8, 10, 12, 14) for m in (24, 120)]
    if args.check:
        if json.loads(CENSUS.read_text()) != panel:
            raise SystemExit('high-word and remainder census differs from the recorded result')
        print('Verified all eight prime-pair panels.')
    else:
        print(json.dumps(panel, indent=2))
