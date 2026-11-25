"""Find the highest fraction of proper gcd hits on a bounded list of prefixes."""

from math import gcd


def scan(n, limit):
    if n < 2 or limit < 0:
        raise ValueError("need an input of at least two and a nonnegative probe limit")

    hits = best_hits = 0
    best_end = first_hit = factor = None
    for end in range(1, limit + 1):
        divisor = gcd(n, end)
        if 1 < divisor < n:
            hits += 1
            if first_hit is None:
                first_hit = end
            if best_end is None or hits * best_end > best_hits * end:
                best_end = end
                best_hits = hits
                factor = divisor

    return dict(gcd_tests=limit, proper_hits=hits, first_hit=first_hit,
                best_hits=best_hits, best_end=best_end, factor=factor)
