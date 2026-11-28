"""Inclusive sum-remainder ranks, averaged over tie orders, on complete small prime bands."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import prod

if __package__:
    from .five_square_prime_census import PRIMES
    from .gap_coverage import primes_through
else:
    from five_square_prime_census import PRIMES
    from gap_coverage import primes_through


def rank_table(signs):
    histogram = {1: 1}
    for p, square in zip(PRIMES, signs):
        groups = [(2, p * (p - 1) // 2)]
        if square:
            groups = [(p, 2), (2, p * (p - 3) // 2)]
        updated = Counter()
        for local_weight, count in groups:
            for old_weight, labels in histogram.items():
                updated[local_weight * old_weight] += labels * count
        histogram = updated

    prior = 0
    doubled_rank = {}
    for weight, count in sorted(histogram.items(), reverse=True):
        doubled_rank[weight] = 2 * prior + count + 1
        prior += count
    return prior + 1, doubled_rank


def census(bits, tables):
    lo, hi = 1 << (bits - 1), 1 << bits
    primes = [p for p in primes_through(hi - 1) if p >= lo and p not in PRIMES]
    flags = {p: tuple(pow(p, (r - 1) // 2, r) == 1 for r in PRIMES) for p in primes}
    patterns = Counter()
    baseline = ranked = 0
    for p, q in combinations(primes, 2):
        if (p * q).bit_length() != 2 * bits:
            continue
        signs = tuple(a == b for a, b in zip(flags[p], flags[q]))
        weight = prod(r if (q - p) % r == 0 else 2 for r in PRIMES)
        random_rank, doubled_ranks = tables[signs]
        baseline += random_rank
        ranked += doubled_ranks[weight]
        patterns[signs] += 1
    return sum(patterns.values()), len(patterns), patterns[(False,) * len(PRIMES)], ranked, baseline


if __name__ == '__main__':
    tables = {s: rank_table(s) for s in product((False, True), repeat=len(PRIMES))}
    for bits in (8, 10, 12, 14):
        count, patterns, all_nonsquare, ranked, baseline = census(bits, tables)
        saving = Fraction(baseline - ranked, baseline)
        print(f'{bits}-bit primes: {count} pairs in {patterns} patterns, '
              f'{all_nonsquare} all-nonsquare, twice ranked total {ranked}, twice random total {baseline}, '
              f'saving {float(saving):.6%}')
