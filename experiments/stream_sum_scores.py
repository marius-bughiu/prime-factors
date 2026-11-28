"""Bounded comparison of lazy ascending and score-ordered sum tests on toy products.

Run with `python3 -m experiments.stream_sum_scores`. Each result validates both
stopping counts against independent counts of residues through a score cutoff.
The shared one-time table checks 25 aligned sums per product residue, using the
625 ordered factor-residue pairs in the imported mod-25 compatibility table.
"""

import json
from dataclasses import asdict, dataclass
from heapq import heapify, heappop, heapreplace
from itertools import combinations
from math import isqrt

from experiments.grouped_offset_sweep import is_prime
from experiments.location_weighted_sum_order import FAVORED
from experiments.toy_period_sum_order import ALLOWED, PERIOD


TWICE_PERIOD = 2 * PERIOD
PERIOD_SQUARED = PERIOD**2
SECOND_DIFFERENCE = 2 * PERIOD_SQUARED


# An entry stores the sum residue and the coefficient in its squared-score key.
# A unit product row has 7 or 10 entries. For the sole nonunit census product
# (35), the public interval contains only one sum, despite its longer table row.
ROWS = tuple(
    tuple((s, 4 if s % 5 in FAVORED.get(n % 5, ()) else 25)
          for s in range((n + 1) % 4, PERIOD, 4) if s % 25 in ALLOWED[n % 25])
    for n in range(PERIOD)
)


@dataclass
class Counts:
    row_entries: int = 0
    seeds: int = 0
    heap_builds: int = 0
    heap_comparisons: int = 0
    heap_replacements: int = 0
    heap_exhaustions: int = 0
    recurrence_additions: int = 0
    key_multiplications: int = 0
    square_tests: int = 0
    peak_heads: int = 0

    def include(self, other):
        for name in self.__dataclass_fields__:
            if name == 'peak_heads':
                self.peak_heads = max(self.peak_heads, other.peak_heads)
            else:
                setattr(self, name, getattr(self, name) + getattr(other, name))


class Head:
    __slots__ = ('s', 'disc', 'delta', 'scale', 'key', 'counts')

    def __init__(self, s, disc, scale, counts):
        self.s = s
        self.disc = disc
        self.delta = TWICE_PERIOD * s + PERIOD_SQUARED
        self.scale = scale
        self.counts = counts
        self.set_key()

    def set_key(self):
        if self.scale:
            self.key = (self.scale * self.disc, self.s)
            self.counts.key_multiplications += 1
        else:
            # For one common coefficient, s and the score are monotone together.
            self.key = (self.s, self.s)

    def __lt__(self, other):
        self.counts.heap_comparisons += 1
        return self.key < other.key

    def advance(self):
        self.s += PERIOD
        self.disc += self.delta
        self.delta += SECOND_DIFFERENCE
        self.counts.recurrence_additions += 3
        self.set_key()


def bounds(n, bits):
    if not 2 <= bits <= 14 or n <= 0 or n.bit_length() != 2 * bits:
        raise ValueError('expected a full-width toy product, with 2 to 14 bits per factor')
    a = 1 << (bits - 1)
    b = 2 * a - 1
    return isqrt(4*n - 1) + 1, min(a + n//a, b + n//b)


def search(n, bits, *, weighted):
    """Return the factors and measured work through the first square, inclusive."""
    lo, hi = bounds(n, bits)
    counts = Counts()
    row = ROWS[n % PERIOD]
    counts.row_entries = len(row)
    different_weights = weighted and n % 5 in FAVORED
    frontier = []
    lo_residue = lo % PERIOD
    four_n = 4 * n
    for residue, scale in row:
        s = lo + (residue - lo_residue) % PERIOD
        if s <= hi:
            frontier.append(Head(s, s*s - four_n, scale if different_weights else 0, counts))
    counts.seeds = counts.peak_heads = len(frontier)
    heapify(frontier)
    counts.heap_builds = 1
    last_with_successor = hi - PERIOD
    while frontier:
        head = frontier[0]
        counts.square_tests += 1
        root = isqrt(head.disc)
        if root*root == head.disc:
            return ((head.s-root)//2, (head.s+root)//2), counts
        if head.s > last_with_successor:
            heappop(frontier)
            counts.heap_exhaustions += 1
        else:
            # Only the minimum changed. Replacing it by its successor restores
            # the heap without allocating a second head for the same progression.
            head.advance()
            heapreplace(frontier, head)
            counts.heap_replacements += 1
    raise ValueError(f'no square in the public toy window for {n}')


def retrospective_ranks(n, bits, target):
    """Independently count both ranks using one exact cutoff per residue class.

    The known true sum enters only this validation step, after both searches.
    Integer square roots implement the weighted cutoff; equal keys use sum order.
    """
    lo, hi = bounds(n, bits)
    if not lo <= target <= hi:
        raise ValueError('target is outside the public sum window')
    four_n = 4*n
    target_scale = 4 if target % 5 in FAVORED.get(n % 5, ()) else 25
    target_key = target_scale * (target**2-four_n)
    ascending = weighted = 0
    for residue, scale in ROWS[n % PERIOD]:
        below_lo = (lo-1-residue)//PERIOD
        ascending += (target-residue)//PERIOD - below_lo
        last = isqrt(four_n + target_key//scale)
        if last > target and scale*(last*last-four_n) == target_key:
            last -= 1
        end = min(last, hi)
        if end >= lo:
            weighted += (end-residue)//PERIOD - below_lo
    return ascending, weighted


def census(bits):
    if not 2 <= bits <= 14:
        raise ValueError('the toy census covers factor widths 2 through 14')
    primes = [p for p in range(1 << (bits-1), 1 << bits) if is_prime(p)]
    total_ascending, total_weighted = Counts(), Counts()
    pairs = 0
    for p, q in combinations(primes, 2):
        n = p*q
        if n.bit_length() != 2*bits:
            continue
        pair_ascending, ascending = search(n, bits, weighted=False)
        pair_weighted, weighted = search(n, bits, weighted=True)
        ranks = retrospective_ranks(n, bits, p+q)
        if pair_ascending != (p, q) or pair_weighted != (p, q):
            raise AssertionError((n, p, q, pair_ascending, pair_weighted))
        if ranks != (ascending.square_tests, weighted.square_tests):
            raise AssertionError((n, ranks, ascending.square_tests, weighted.square_tests))
        pairs += 1
        total_ascending.include(ascending)
        total_weighted.include(weighted)
    return {'bits': bits, 'pairs': pairs,
            'ascending': asdict(total_ascending), 'weighted': asdict(total_weighted)}


if __name__ == '__main__':
    for width in range(2, 15):
        print(json.dumps(census(width)), flush=True)
