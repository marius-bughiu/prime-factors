"""Rank the same factor-sum rows with reusable fixed-point bounds on their endpoints."""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations
import json
from math import isqrt, lcm
from pathlib import Path
from typing import NamedTuple

from experiments import high_word_suffix_ranking as exact
from experiments.high_word_sum_ranking import check_midpoint, gap_interval
from scripts.factor import primes_through


CENSUS = Path(__file__).resolve().parents[1] / 'research/fractional-word-ranking.json'
PRECISIONS = (8, 12)


class RootTable(NamedTuple):
    bits: int
    floors: tuple
    ceilings: tuple

    def bracket(self, x):
        """Return inclusive bounds on isqrt(x) and the number of table values read."""
        if x < 0:
            raise ValueError('expected a nonnegative radicand')
        shift = max(0, (x.bit_length() - self.bits + 1) // 2)
        index = x >> (2 * shift)
        lower = (self.floors[index] << shift) >> self.bits
        if shift == 0:
            return lower, lower, 1
        # x < (index + 1) * 2^(2*shift). Round the strict upper bound down.
        upper = ((self.ceilings[index + 1] << shift) - 1) >> self.bits
        return lower, upper, 2


@lru_cache(maxsize=2)
def root_table(k):
    """One row per leading index, including the upper neighbor of the last index."""
    if k < 1:
        raise ValueError('expected a positive table precision')
    floors = tuple(isqrt(i << (2 * k)) for i in range((1 << k) + 1))
    ceilings = tuple(root + (root * root != (i << (2 * k))) for i, root in enumerate(floors))
    return RootTable(k, floors, ceilings)


def table_cost(k):
    entries = len(root_table(k).floors)
    return dict(root_table_entries=entries, table_build_small_roots=entries,
                max_table_radicand_bits=3 * k + 1)


class Candidate(NamedTuple):
    midpoint: int
    minimum: int
    maximum: int
    residues: tuple


def propose(bits, word, modulus, residue, k):
    """Return the earliest maximizer of positive row support within the ranked block."""
    if bits < 2 or not 0 <= residue < modulus:
        raise ValueError('expected a valid factor width and product remainder')
    base = 1 << bits
    if not base // 2 <= word < base:
        raise ValueError('expected a full-width product')
    lower = word * base
    upper = lower + base - 1
    first = isqrt(upper)
    period = lcm(2, modulus)
    classes = exact.square_classes(modulus)
    table = root_table(k)
    work = dict(period=period, rows=period + 1, table_entries=period, precision=k,
                initial_roots=1, refinement_roots=0, root_brackets=0, table_lookups=0,
                residue_class_counts=0, maximum_proved=bits >= 14 and base >= 4096 * period ** 3,
                **table_cost(k))

    def bracket(value):
        low, high, reads = table.bracket(value)
        work['root_brackets'] += 1
        work['table_lookups'] += reads
        return low, high

    def count(low, high, residues):
        if high < low:
            return 0
        work['residue_class_counts'] += len(residues)
        return sum((high - r) // period - (low - 1 - r) // period for r in residues)

    candidates = []
    for midpoint in range(first, first + period + 1):
        residues = exact.allowed_gaps(classes, modulus, residue, midpoint)
        square = midpoint * midpoint
        if not residues or square < lower or not base // 2 <= midpoint < base:
            continue
        cap = min(midpoint - base // 2, base - 1 - midpoint)
        end_low, end_high = bracket(square - lower)
        if square > upper:
            left, right = bracket(square - upper - 1)
            start_low, start_high = left + 1, right + 1
        else:
            start_low = start_high = 1
        maximum = count(start_low, min(cap, end_high), residues)
        if maximum:
            minimum = count(start_high, min(cap, end_low), residues)
            candidates.append(Candidate(midpoint, minimum, maximum, residues))

    # A later tie cannot beat the earliest row attaining the largest guaranteed score.
    contenders = []
    if candidates:
        anchor = max(candidates, key=lambda c: c.minimum)
        contenders = [c for c in candidates if c.maximum > anchor.minimum or
                      (c.maximum == anchor.minimum and c.midpoint <= anchor.midpoint)]
    best = None
    if len(contenders) == 1 and contenders[0].minimum > 0:
        best = contenders[0].midpoint
    else:
        best_score = 0
        for candidate in contenders:
            if candidate.maximum <= best_score:
                continue
            score = candidate.minimum
            if score != candidate.maximum:
                low, high, roots = gap_interval(base, lower, upper, candidate.midpoint)
                work['refinement_roots'] += roots
                score = count(low, high, candidate.residues)
            if score > best_score:
                best = candidate.midpoint
                best_score = score
    work['midpoint'] = best
    work['setup_roots'] = work['initial_roots'] + work['refinement_roots']
    return work


def search(n, bits, modulus, k):
    """Use only the product, factor width, modulus and table precision."""
    if n < 3 or n % 2 == 0 or bits < 2:
        raise ValueError('expected an odd product with a common factor width of at least two')
    work = propose(bits, n >> bits, modulus, n % modulus, k)
    factor, tests = (None, 0) if work['midpoint'] is None else check_midpoint(n, work['midpoint'])
    work['square_tests'] = tests
    return factor, work


class ReadingCost(NamedTuple):
    initial_roots: int
    refinement_roots: int
    root_brackets: int
    table_lookups: int
    residue_class_counts: int
    exact_ranking_setup_roots: int


def census(bits, modulus):
    """Verify the original winner once per occupied reading, then score each prime pair."""
    base = 1 << bits
    primes = [p for p in primes_through(base - 1) if p >= base // 2]
    readings = {}
    per_reading = {k: Counter() for k in PRECISIONS}
    per_product = {k: Counter() for k in PRECISIONS}
    for p, q in combinations(primes, 2):
        n = p * q
        word, residue = n >> bits, n % modulus
        if word < base // 2:
            continue
        key = word, residue
        if key not in readings:
            original = exact.propose(bits, word, modulus, residue)
            midpoint = original['midpoint']
            costs = {}
            for k in PRECISIONS:
                work = propose(bits, word, modulus, residue, k)
                if work['midpoint'] != midpoint:
                    raise ValueError(f'original and bounded rankings disagree at {bits, key, k}')
                costs[k] = ReadingCost(work['initial_roots'], work['refinement_roots'],
                                       work['root_brackets'], work['table_lookups'],
                                       work['residue_class_counts'], original['setup_roots'])
                per_reading[k].update(costs[k]._asdict())
            readings[key] = midpoint, costs
        midpoint, costs = readings[key]
        start = 1 + isqrt(n - 1)
        true_midpoint = (p + q) // 2
        prefix = exact.local_prefix(modulus, residue)
        needed = exact.prefix_count(true_midpoint + 1, prefix) - exact.prefix_count(start, prefix)
        square_tests = int(midpoint is not None and midpoint >= start)
        ranked = midpoint == true_midpoint
        for k, cost in costs.items():
            # Direct Fermat charges its own start root, leaving the refinements and final test.
            budget = cost.refinement_roots + square_tests
            direct = needed <= budget
            per_product[k].update(cost._asdict())
            per_product[k].update(pairs=1, square_tests=square_tests, ranked=ranked,
                                  direct=direct, ranked_only=ranked and not direct,
                                  direct_only=direct and not ranked,
                                  direct_square_tests=min(needed, budget),
                                  no_refinement=cost.refinement_roots == 0)

    return [dict(factor_bits=bits, modulus=modulus, precision=k, occupied_readings=len(readings),
                 per_reading=dict(per_reading[k]), per_product=dict(per_product[k]))
            for k in PRECISIONS]


def report():
    return dict(tables=[dict(precision=k, **table_cost(k)) for k in PRECISIONS],
                panels=[row for bits in (8, 10, 12, 14) for modulus in (24, 120)
                        for row in census(bits, modulus)])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = report()
    if args.check:
        if json.loads(CENSUS.read_text()) != result:
            raise SystemExit('fractional word census differs from the recorded result')
        print('Verified all sixteen precision, modulus and prime-width panels.')
    else:
        print(json.dumps(result, indent=2))
