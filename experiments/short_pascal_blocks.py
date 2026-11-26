"""Batch the numerator of the short Pascal row on a wheel of trial divisors.

For distinct equal-width primes p<q, lower<=p<=row<q and the binomial
denominator is a unit. Once wheel primes have been checked, the gcd of
the retained numerator factors therefore equals p on a complete interval.
This uses classical Pollard–Strassen multipoint evaluation and a fixed
small-prime wheel (Costa–Harvey, https://arxiv.org/abs/1201.2116).
"""
from argparse import ArgumentParser
from bisect import bisect_left
from json import dumps
from math import gcd, isqrt

from .short_pascal_row import interval
from .universal_norm_batch import modular_product
from .wide_modulus import product_tree, values_at


WHEEL_PRIMES = {1: (), 2: (2,), 30: (2, 3, 5), 210: (2, 3, 5, 7)}


def search(n, wheel, max_side):
    """Visit the first budgeted wheel candidates. Cap both degree and point count."""
    if wheel not in WHEEL_PRIMES or max_side < 0:
        raise ValueError('use wheel 1, 2, 30 or 210 and a nonnegative side cap')
    lower, row = interval(n)
    column = max(0, row+1-lower)
    residues = [i for i in range(wheel) if gcd(i, wheel) == 1]
    phi = len(residues)

    def count_before(stop):
        cycles, rem = divmod(stop, wheel)
        return cycles*phi + bisect_left(residues, rem)

    def candidate(i):
        cycle, slot = divmod(i, phi)
        return cycle*wheel + residues[slot]

    first = count_before(lower)
    total = max(0, count_before(row+1)-first)
    square_side = 1+isqrt(total-1) if total else 0
    target_side = min(total, phi*((square_side+phi-1)//phi))
    side = min(max_side, target_side)
    degree = (side//phi)*phi
    # A cap below one wheel period allows only direct edge terms.
    take = min(total, side*degree if degree else side)
    base = ((lower+wheel-1)//wheel)*wheel
    head = min(take, count_before(base)-first)
    points, tail = divmod(take-head, degree) if degree else (0, take-head)
    stride = (degree//phi)*wheel
    work = dict(wheel_residue_gcds=wheel, wheel_gcds=1, wheel_prime_tests=0,
                roots=0, points=0, head_terms=0, tail_terms=0,
                batch_gcds=0, refinement_gcds=0, recurrence_steps=0)
    result = dict(factor=None, n=str(n), wheel=wheel, max_side=max_side,
                  lower=str(lower), row=str(row), column=str(column),
                  literal_recurrence_steps=str(min(column, row-column)),
                  target_side=str(target_side), candidates=str(total),
                  checked_candidates=0, remaining_candidates=str(total),
                  last_checked=None, product_residue=None, outcome='side_limit',
                  work=work)
    common = gcd(wheel, n)
    if common > 1:
        for prime in WHEEL_PRIMES[wheel]:
            work['wheel_prime_tests'] += 1
            if prime < n and common % prime == 0:
                return dict(result, factor=prime, outcome='wheel_factor')
    if not take:
        return dict(result, outcome='interval_exhausted' if total == 0 else 'side_limit')

    block_values = []
    if points:
        # For each base+j*stride the roots -offset give every surviving
        # integer in that complete block exactly once.
        offsets = [i*wheel+r for i in range(degree//phi) for r in residues]
        poly = product_tree([-x for x in offsets], n)[-1][0]
        block_values = values_at(poly, [base+j*stride for j in range(points)], n)
        work.update(roots=degree, points=points)
    head_values = [candidate(first+i) for i in range(head)]
    tail_values = [candidate(first+take-tail+i) for i in range(tail)]
    work.update(head_terms=head, tail_terms=tail, batch_gcds=1)
    batches = [*head_values, *block_values, *tail_values]
    product = modular_product(batches, n)
    common = gcd(product, n)
    result.update(checked_candidates=take, remaining_candidates=str(total-take),
                  last_checked=str(candidate(first+take-1)), product_residue=str(product),
                  outcome='interval_exhausted' if take == total else 'side_limit')
    if 1 < common < n:
        return dict(result, factor=common, outcome='interval_gcd')
    if common == n:
        # Only needed outside the distinct equal-width prime promise.
        for i, value in enumerate(batches):
            work['refinement_gcds'] += 1
            divisor = gcd(value, n)
            if 1 < divisor < n:
                return dict(result, factor=divisor, outcome='refined_gcd')
            if divisor == n and head <= i < head+points:
                for offset in offsets:
                    work['refinement_gcds'] += 1
                    divisor = gcd(base+(i-head)*stride+offset, n)
                    if 1 < divisor < n:
                        return dict(result, factor=divisor, outcome='refined_gcd')
        return dict(result, outcome='whole_modulus')
    return result


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--wheel', type=int, choices=WHEEL_PRIMES, default=30)
    parser.add_argument('--max-side', type=int, default=128)
    args = parser.parse_args()
    print(dumps(search(args.n, args.wheel, args.max_side), indent=2))
