"""Check two sum orders on fixed small prime populations.

At 9, 10 and 12 bits, both orders perform exact discriminant square tests.
At 13 through 15 bits, use the known true sum to count where each order
would stop. Those retrospective ranks include the successful test.
"""

import json
from bisect import bisect_left, bisect_right
from dataclasses import asdict, dataclass
from functools import lru_cache
from itertools import combinations
from math import isqrt

from experiments.grouped_offset_sweep import is_prime
from experiments.toy_residue_order_cost import first_square


PERIOD = 100
ALLOWED = [set() for _ in range(25)]
for a in range(25):
    for b in range(25):
        ALLOWED[a*b % 25].add((a+b) % 25)
SQUARES = {a*a % 25 for a in range(25)}
UNIT_SQUARES = SQUARES - {0}


@lru_cache(maxsize=10000)
def period_offsets(product_mod, start_mod):
    """Offsets in the physically aligned 100-integer block starting at start_mod."""
    offsets = []
    singular = []
    for offset in range(PERIOD):
        s = start_mod + offset
        if s % 4 == (product_mod+1) % 4 and s % 25 in ALLOWED[product_mod % 25]:
            offsets.append(offset)
            if (s*s-4*product_mod) % 5 == 0:
                singular.append(offset)
    if len(offsets) != 7 or len(singular) != 2:
        raise AssertionError('an eligible complete block must have two singular and five other sums')
    return offsets, singular


@dataclass(frozen=True)
class Ranks:
    ascending: int
    prioritized: int
    block: int
    clipped: bool
    omitted_priority: int


def retrospective_ranks(n, lo, hi, true_sum):
    """Use the true sum as the target and count complete earlier blocks exactly."""
    if not lo <= true_sum <= hi:
        raise AssertionError('true sum outside the public window')
    offsets, singular = period_offsets(n % PERIOD, lo % PERIOD)
    block, pos = divmod(true_sum-lo, PERIOD)
    index = bisect_left(offsets, pos)
    if index == len(offsets) or offsets[index] != pos:
        raise AssertionError('true sum failed the public residue conditions')
    end = min(PERIOD-1, hi-lo-PERIOD*block)
    before = block*len(offsets)
    singular_through_target = bisect_right(singular, pos)
    singular_in_block = bisect_right(singular, end)
    if pos in singular:
        local_rank = singular_through_target
        omitted_priority = 0
    else:
        local_rank = singular_in_block + index + 1 - singular_through_target
        omitted_priority = len(singular) - singular_in_block
    return Ranks(before+index+1, before+local_rank, block, end<PERIOD-1, omitted_priority)


def check_direct(n, lo, hi, expected_pair, ranks):
    """Generate the same candidates independently via square discriminants modulo 25."""
    start = lo + (n+1-lo) % 4
    ascending = [s for s in range(start, hi+1, 4) if (s*s-4*n) % 25 in SQUARES]
    prioritized = sorted(ascending, key=lambda s: ((s-lo)//PERIOD, (s*s-4*n) % 5 != 0))
    for menu, expected_rank in ((ascending, ranks.ascending), (prioritized, ranks.prioritized)):
        tests, factors = first_square(n, menu)
        if tests != expected_rank or factors != expected_pair:
            raise AssertionError((n, tests, expected_rank, factors, expected_pair))


@dataclass
class Counts:
    eligible: int = 0
    earlier: int = 0
    tied: int = 0
    later: int = 0
    ascending_tests: int = 0
    prioritized_tests: int = 0
    hits_in_clipped_block: int = 0
    ranks_changed_by_clipping: int = 0

    def record(self, ranks):
        change = ranks.prioritized - ranks.ascending
        if not -5 <= change <= 2:
            raise AssertionError(('change outside the two-singular, five-regular block bounds', change))
        self.eligible += 1
        self.earlier += change < 0
        self.tied += change == 0
        self.later += change > 0
        self.ascending_tests += ranks.ascending
        self.prioritized_tests += ranks.prioritized
        self.hits_in_clipped_block += ranks.clipped
        self.ranks_changed_by_clipping += ranks.omitted_priority > 0


def census(bits, direct):
    a = 2**(bits-1)
    b = 2*a-1
    primes = [p for p in range(a, b+1) if is_prime(p)]
    groups = {'square': Counts(), 'one': Counts()}
    examples = {}
    for p, q in combinations(primes, 2):
        n = p*q
        if n % 25 not in UNIT_SQUARES:
            continue
        lo = isqrt(4*n-1)+1
        hi = min(a+n//a, b+n//b)
        ranks = retrospective_ranks(n, lo, hi, p+q)
        if direct:
            check_direct(n, lo, hi, (p,q), ranks)
        groups['square'].record(ranks)
        if n % 25 == 1:
            groups['one'].record(ranks)
        # Retain the first lexicographic example of each phenomenon at 12 bits.
        if bits == 12:
            change = ranks.prioritized-ranks.ascending
            for label, select in (('five_earlier', change == -5), ('two_later', change == 2),
                                  ('clipping_changes_rank', ranks.block > 0 and ranks.omitted_priority > 0)):
                if select and label not in examples:
                    examples[label] = dict(n=str(n), factors=[str(p),str(q)], lo=lo, hi=hi,
                                           true_sum=p+q, **asdict(ranks))
    if direct and groups['square'].ranks_changed_by_clipping == 0:
        raise AssertionError('direct controls must exercise upper-end clipping')
    result = dict(bits=bits, mode='direct square tests checked against ranks' if direct else
                  'retrospective ranks using known sums', prime_count=len(primes),
                  distinct_pairs=len(primes)*(len(primes)-1)//2,
                  groups={key: asdict(count) for key, count in groups.items()})
    if examples:
        result['examples'] = examples
    return result


if __name__ == '__main__':
    for width in (9, 10, 12, 13, 14, 15):
        print(json.dumps(census(width, direct=width <= 12)), flush=True)
