"""Guess one factor sum using only the high product word and the common factor width."""

import argparse
from collections import Counter, defaultdict
from itertools import combinations
import json
from math import isqrt
from pathlib import Path

from scripts.factor import primes_through


ROOT = Path(__file__).resolve().parents[1]
CENSUS = ROOT / 'research/high-word-sum-ranking.json'


def gap_interval(base, lower, upper, midpoint):
    """Inclusive physical half-gap interval and number of integer square roots evaluated."""
    square = midpoint * midpoint
    if square < lower or not base // 2 <= midpoint < base:
        return 1, 0, 0
    high_gap = min(isqrt(square - lower), midpoint - base // 2, base - 1 - midpoint)
    excess = square - upper
    low_gap = 1 if excess <= 0 else 1 + isqrt(excess - 1)
    return low_gap, high_gap, 1 + int(excess > 0)


def row_count(base, lower, upper, midpoint):
    """Count distinct sorted odd factor pairs in the word and charge the roots used."""
    low_gap, high_gap, roots = gap_interval(base, lower, upper, midpoint)
    first = low_gap + (midpoint + 1 - low_gap) % 2
    return max(0, 1 + (high_gap - first) // 2), roots


def propose(factor_bits, word):
    if factor_bits < 1:
        raise ValueError('expected a positive factor width')
    base = 1 << factor_bits
    if not base // 2 <= word < base:
        raise ValueError('expected a full-width product of two equal-width odd factors')
    lower = base * word
    upper = lower + base - 1
    midpoint = isqrt(upper)
    # The upper word endpoint is 3 modulo 4 and hence is never a square.
    lower_count, lower_roots = row_count(base, lower, upper, midpoint)
    upper_count, upper_roots = row_count(base, lower, upper, midpoint + 1)
    choice = midpoint + int(upper_count > lower_count)
    return dict(midpoint=choice, floor_midpoint=midpoint, counts=[lower_count, upper_count],
                setup_roots=1 + lower_roots + upper_roots)


def check_midpoint(n, midpoint):
    discriminant = midpoint * midpoint - n
    if discriminant < 0:
        return None, 0
    gap = isqrt(discriminant)
    if gap * gap == discriminant and 1 < midpoint - gap < midpoint + gap:
        return midpoint - gap, 1
    return None, 1


def search(n, factor_bits):
    if n < 3 or n % 2 == 0 or factor_bits < 2:
        raise ValueError('expected an odd product with a common factor width of at least two')
    work = propose(factor_bits, n >> factor_bits)
    factor, work['square_tests'] = check_midpoint(n, work['midpoint'])
    return factor, work


def census(bits):
    base = 1 << bits
    primes = [p for p in primes_through(base - 1) if p >= base // 2]
    actual = defaultdict(Counter)
    ranked = {}
    hits = earliest_hits = fermat_hits = extra = lost = 0
    for p, q in combinations(primes, 2):
        n = p * q
        h = n // base
        if h < base // 2:
            continue
        if h not in ranked:
            ranked[h] = propose(bits, h)
        choice = ranked[h]
        true_midpoint = (p + q) // 2
        actual[h][true_midpoint] += 1
        hit = true_midpoint == choice['midpoint']
        first_occupied = choice['floor_midpoint'] + int(choice['counts'][0] == 0)
        earliest_hits += true_midpoint == first_occupied
        baseline = true_midpoint == 1 + isqrt(n - 1)
        hits += hit
        fermat_hits += baseline
        extra += hit and not baseline
        lost += baseline and not hit
    # These two bounds use the known prime labels only after the predictions are fixed.
    prime_oracle = sum(max(counts.values()) for counts in actual.values())
    near_oracle = sum(max(counts[ranked[h]['floor_midpoint'] + j] for j in (0, 1))
                      for h, counts in actual.items())
    return dict(factor_bits=bits, prime_pairs=sum(sum(v.values()) for v in actual.values()),
                occupied_words=len(actual), ranked=hits, first_occupied=earliest_hits,
                first_fermat=fermat_hits, ranked_only=extra, fermat_only=lost,
                oracle_best_per_word=prime_oracle, oracle_best_of_two=near_oracle)


def verify_small_words():
    """Compare the two-row maximum with every midpoint of every small high word."""
    words = 0
    for bits in range(1, 14):
        base = 1 << bits
        rows = defaultdict(Counter)
        odd_factors = range(base // 2 | 1, base, 2)
        for p, q in combinations(odd_factors, 2):
            word = p * q // base
            if word >= base // 2:
                rows[word][(p + q) // 2] += 1
        for word in range(base // 2, base):
            prediction = propose(bits, word)
            floor = prediction['floor_midpoint']
            actual = rows[word]
            if (prediction['counts'] != [actual[floor], actual[floor + 1]]
                    or max(prediction['counts']) != max(actual.values(), default=0)):
                raise ValueError(f'incorrect row count at width {bits}, word {word}')
            words += 1
    return words


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    report = [census(bits) for bits in (8, 10, 12, 14)]
    if args.check:
        if json.loads(CENSUS.read_text()) != report:
            raise SystemExit('high-word census differs from the recorded result')
        print(f'Verified four prime-pair censuses and all {verify_small_words():,} smaller words.')
    else:
        print(json.dumps(report, indent=2))
