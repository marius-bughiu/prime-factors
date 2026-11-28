"""Charge filters on the old score-ordered prefix through each known toy prime sum."""
from itertools import combinations
from math import isqrt

from experiments.grouped_offset_sweep import is_prime
from experiments.stream_sum_scores import ROWS, bounds, retrospective_ranks

PRIMES = (3, 7, 11, 13, 17, 19)
TESTS = tuple((p * p, {x * x % (p * p) for x in range(p * p)}) for p in PRIMES)


def prefix_counts(p, q):
    """Use known factors only to identify the inclusive stopping point for counting."""
    n = p * q
    target = p + q
    lo, hi = bounds(n, p.bit_length())
    row = ROWS[n % 100]
    limit = (dict(row)[target % 100] * (target * target - 4 * n), target)
    prior = kept = lookups = 0
    for residue, scale in row:
        for s in range(lo + (residue - lo) % 100, hi + 1, 100):
            disc = s * s - 4 * n
            if (scale * disc, s) > limit:
                break
            prior += 1
            for m, squares in TESTS:
                lookups += 1
                if disc % m not in squares:
                    break
            else:
                kept += 1
                if isqrt(disc)**2 == disc and s != target:
                    raise AssertionError('Unexpected additional square hit in the window')
    if prior != retrospective_ranks(n, p.bit_length(), target)[1]:
        raise AssertionError('Baseline disagrees with the independent per-residue count')
    if kept < 1 or any((target * target - 4 * n) % m not in squares for m, squares in TESTS):
        raise AssertionError('Lost the true factor sum')
    return prior, kept, lookups


def census(bits):
    primes = [p for p in range(1 << (bits - 1), 1 << bits) if is_prime(p)]
    old = new = lookups = total = 0
    largest = (0, 0, 0, 0, 0)
    for p, q in combinations(primes, 2):
        if (p * q).bit_length() != 2 * bits:
            continue
        prior, kept, work = prefix_counts(p, q)
        total += 1
        old += prior
        new += kept
        lookups += work
        if prior - kept > largest[0]:
            largest = prior - kept, p, q, prior, kept
    return total, old, new, lookups, largest


if __name__ == '__main__':
    for width in (10, 12, 14):
        print(width, census(width), flush=True)
