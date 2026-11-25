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


def scan_sum_rectangles(n, limit):
    """Score all 1 <= a <= b <= min(limit,n), with positive draws x,y.

    Whole periods in either coordinate have the same hit fraction regardless
    of the other draw, so one period per side suffices for a global maximum.
    Equal fractions keep the first rectangle in increasing (a,b) order.
    """
    if n < 2 or limit < 0:
        raise ValueError("need an input of at least two and a nonnegative rectangle limit")

    side = min(limit, n)
    first_hit_sum = first_hit_gcd = None
    prefix = [0] * (2*side + 1)
    for total in range(2, 2*side + 1):
        divisor = gcd(n, total)
        proper = 1 < divisor < n
        prefix[total] = prefix[total - 1] + proper
        if proper and first_hit_gcd is None:
            first_hit_sum, first_hit_gcd = total, divisor

    hits_by_column = [0] * (side + 1)
    best_a = best_b = None
    best_hits, best_area = 0, 1
    rectangles = 0
    for a in range(1, side + 1):
        for b in range(a, side + 1):
            # The new row uses the b consecutive sums from a+1 through a+b.
            hits_by_column[b] += prefix[a+b] - prefix[a]
            hits = hits_by_column[b]
            area = a*b
            rectangles += 1
            if best_a is None or hits * best_area > best_hits * area:
                best_a, best_b = a, b
                best_hits, best_area = hits, area

    cutoff_gcd = gcd(n, best_b + 1) if best_b is not None else None
    if cutoff_gcd is not None and 1 < cutoff_gcd < n:
        factor, factor_source = cutoff_gcd, "cutoff"
    elif first_hit_gcd is not None:
        factor, factor_source = first_hit_gcd, "sum_table"
    else:
        factor, factor_source = None, None
    return dict(limit=limit, scanned_side=side, full_period_scanned=side == n,
                sum_gcd_tests=max(0, 2*side - 1), proper_sums=prefix[-1],
                first_hit_sum=first_hit_sum, first_hit_gcd=first_hit_gcd,
                rectangles_tested=rectangles, best_a=best_a, best_b=best_b,
                best_hits=best_hits, cutoff_gcd_tests=int(cutoff_gcd is not None),
                cutoff_gcd=cutoff_gcd, factor_source=factor_source, factor=factor)
