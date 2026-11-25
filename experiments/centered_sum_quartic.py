"""Positive quartic factor remainders using the short interval for x+y."""

from collections import Counter
from math import gcd, isqrt, prod
from time import perf_counter

from .unit_quartic_probe import checked_polynomial, factor_roots, short_relation


def windows(n):
    """Bounds obtained solely from the input and the equal prime bit width."""
    if n < 9 or gcd(n, 30) != 1:
        raise ValueError('expected a product >= 9 coprime to 30')
    bits = (n.bit_length()+1)//2
    first = 1 << (bits-1)
    last = 2*first-1
    low, high = max(first, (n+last-1)//last), min(last, n//first)
    sum_low = 1+isqrt(4*n-1)
    if low > high or high+n//high < sum_low:
        raise ValueError('empty equal-width factor window')
    sum_high = high+n//high
    radius = max(1, (high-low+1)//2)
    half_sum_radius = max(1, (sum_high-sum_low+3)//4)
    center = (low+high)//2
    sum_center = (sum_low+sum_high)//2
    return low, high, center, sum_center, radius, half_sum_radius


def centered_coordinates(trace, n, center, sum_center, s):
    """Write d*y²+b*y+e+a*x+c*x² in 1,T,Z,T²−2s²,ZT."""
    d, b, e, a, c = trace
    squared = d
    mixed = c-d
    linear_sum = b + 2*sum_center*squared + center*mixed
    linear_factor = a-linear_sum + 2*sum_center*squared + (sum_center+center)*mixed
    constant = (e + sum_center*linear_sum + center*linear_factor
                - (2*n + sum_center**2 - 2*s**2)*squared - (n+center*sum_center)*mixed)
    return [constant, linear_sum, linear_factor, squared, mixed]


def probe(n, u=1):
    low, high, c, h, radius, s = windows(n)
    scales = [1, 2*s, radius, 2*s*s, 2*s*radius]
    weight = prod(scales)
    exponent = 3
    while 3125*weight >= 12960 << (10*exponent):
        exponent += 1
    radix = 1 << exponent
    if not 0 < u < radix or u % 2 == 0:
        raise ValueError('expected an odd residue in the radix')
    start = perf_counter()
    work = Counter()
    trace, size = short_relation(n, u, radix,
                                 lambda row: centered_coordinates(row, n, c, h, s), scales, work)
    polynomial, checks = checked_polynomial(n, u, radix, trace)
    pairs, hits = factor_roots(n, u, radix, polynomial, [(low, high)], work)
    total = (radix//2 + (4 if n%8 == 1 else 0))//2
    return dict(radix_exponent=exponent, residue=str(u), factor_min=str(low), factor_max=str(high),
                factor_center=str(c), sum_center=str(h), factor_radius=str(radius),
                half_sum_radius=str(s), weight_product=str(weight), weighted_l1=str(size),
                trace_coefficients=list(map(str, trace)), local_remainders=checks,
                total_groups=str(total), unchecked_groups=str(total-1), candidate_factors=hits,
                pairs=[[str(p),str(q)] for p,q in sorted(pairs)], work=dict(work),
                search_seconds=perf_counter()-start)


if __name__ == '__main__':
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--residue', type=int, default=1)
    args = parser.parse_args()
    print(json.dumps(probe(args.n, args.residue), indent=2))
