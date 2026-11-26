"""Finite coverage bounds for signed, stride-24 weighted square dependencies.

Run ``python3 -m experiments.weighted_subset_budget``. All output bounds use
integer arithmetic. No products, factors or putative relation lists are sampled.
"""
import json
from bisect import bisect_left
from fractions import Fraction
from math import gcd, isqrt

from experiments.gap_coverage import primes_through

X = 2**1023
POPULATION_CONSTANT = 21_000_000
UNIT_CLASSES = (1, 5, 7, 11, 13, 17, 19, 23)
SMALL_LIMIT = 2**16
SMALL_PRIMES = primes_through(SMALL_LIMIT-1)
WHEEL = 30_030
COPRIMES = tuple(i for i in range(WHEEL) if gcd(i, WHEEL) == 1)
PRECISION = 80
DENOMINATOR = 64


def ceildiv(a, b):
    return (a+b-1)//b


def wheel_below(n):
    periods, remainder = divmod(n, WHEEL)
    return periods*len(COPRIMES)+bisect_left(COPRIMES, remainder)


def prime_bins(bit_budget):
    """An earliest possible list of prime factors, compressed into (lower, count).

    Each selected prime in [2^j,2^(j+1)) costs at least j support bits.
    The central binomial bound and subinterval capacities cap the prefix
    count in that octave. Every actual sorted prime support is dominated.
    """
    bins = []
    remaining = bit_budget
    j = 1
    while remaining >= j:
        low = 2**j
        width = max(1, low//16)
        # At the first octave rely only on the exact sieve (its left endpoint is prime).
        octave_room = 2*low//j if low >= SMALL_LIMIT else low
        for start in range(low, 2*low, width):
            end = start+width
            if low < SMALL_LIMIT:
                count = bisect_left(SMALL_PRIMES, end)-bisect_left(SMALL_PRIMES, start)
            else:
                count = wheel_below(end)-wheel_below(start)
            used = min(count, octave_room, remaining//j)
            if used:
                bins.append((start, used))
                octave_room -= used
                remaining -= j*used
            if octave_room == 0 or remaining < j:
                break
        j += 1
    return bins


def reciprocal_upper(x, numerator):
    """Ceiling of 2^PRECISION / x^(numerator/64), by six integer square roots."""
    q = (1 << (PRECISION*DENOMINATOR)) // x**numerator
    for _ in range(6):
        q = isqrt(q)
    exact = q**DENOMINATOR*x**numerator == 1 << (PRECISION*DENOMINATOR)
    return q if exact else q+1


def bound(k, ranks):
    if not (1 <= k < X and 1 <= ranks and 24*ranks < 2*X):
        raise ValueError('require 1 <= k < X and 1 <= ranks with 24*ranks < 2*X')
    h = 1+isqrt(k-1)
    width = max(1, ranks//h)
    height = 24*ranks
    y = height*(8*X*h+height)
    # In one cell, the distance from either extreme label to 2*sqrt(r)*cell_start.
    deviation = height+2*h*width
    determinant = 2*k*deviation*(8*X*h+deviation)
    counts = []
    for rho in UNIT_CLASSES:
        count = 0
        for r in range(1, k+1):
            stride = gcd(24, 2*(r+rho))
            count += 2*ranks+1+isqrt(4*r*width**2)//stride
        counts.append(count)
    support_bits = (max(counts)-1)*(determinant-1).bit_length()
    bins = prime_bins(support_bits)
    label_cells = ceildiv(X, width)*sum(counts)
    y_bits = (y-1).bit_length()
    # log_2(e) < 1443/1000, using four positive terms of the atanh(1/3) series.
    log2_lower = sum(Fraction(2, (2*i+1)*3**(2*i+1)) for i in range(4))
    assert log2_lower > Fraction(1000, 1443)
    choices = []
    for num in range(DENOMINATOR//2, DENOMINATOR):
        cost = sum(n*reciprocal_upper(x, num) for x, n in bins)
        correction = Fraction(1443*cost, 1000*(1 << PRECISION))
        fiber_log = Fraction(num*y_bits, DENOMINATOR)+correction
        choices.append((fiber_log, num, correction))
    fiber_log, num, correction = min(choices)
    fiber_bits = ceildiv(fiber_log.numerator, fiber_log.denominator)
    # Each possible |D| gives at most two products. Both possible gcd signs
    # are already included in this necessary condition.
    unit_products = 2*label_cells*(1 << fiber_bits)
    # p is either prime dividing the label, c=A/p and e=(A²−4rn)/p is signed.
    nonunit_products = X*k*(4*h+height//X)*(2*(y//X)+1)
    numerator = POPULATION_CONSTANT*(unit_products+nonunit_products)
    guarantee = (X**2//numerator).bit_length()-1 if numerator <= X**2 else None
    return dict(weight_cap=k, ranks_per_side=ranks, max_rows_per_input=2*k*ranks,
                continuous_height=height, cell_width=width, catalogue_counts_by_residue=counts,
                label_cell_bits=(label_cells-1).bit_length(), excess_bits=y_bits,
                determinant_bits=(determinant-1).bit_length(), support_bits=support_bits,
                last_prime_bin_lower=bins[-1][0], theta_numerator=num,
                theta_denominator=DENOMINATOR,
                correction_bits=ceildiv(correction.numerator, correction.denominator),
                absolute_excess_values_bits=fiber_bits,
                unit_product_bits=(unit_products-1).bit_length(),
                nonunit_product_bits=(nonunit_products-1).bit_length(),
                fraction_below_inverse_two_power=guarantee)


if __name__ == '__main__':
    print(json.dumps([bound(k, k) for k in (16, 64, 256, 1024, 4096)], indent=2))
