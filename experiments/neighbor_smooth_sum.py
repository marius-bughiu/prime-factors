"""Test a single factor-sum candidate from a public integer divisible by the proposed sum."""

from math import isqrt

from experiments.gap_coverage import primes_through


def balanced_factor_from_sum(n, candidate_sum):
    square = candidate_sum**2
    in_range = candidate_sum % 2 == 0 and 4*n <= square and 2*square <= 9*n
    factor = None
    if in_range:
        difference = isqrt(square - 4*n)
        smaller = (candidate_sum - difference) // 2
        if difference**2 == square - 4*n and 1 < smaller < n and smaller * (candidate_sum-smaller) == n:
            factor = smaller
    return factor, int(in_range)


def search(n, prime_limit, inverse_gap=0):
    if n < 3 or n % 2 == 0 or prime_limit < 2:
        raise ValueError("need an odd product of at least three and a prime cutoff of at least two")

    source = n + 1 if inverse_gap == 0 else (n + 1)**2 + n * inverse_gap**2
    residual = source
    divisions = checks = 0
    for prime in primes_through(prime_limit):
        while True:
            checks += 1
            quotient, remainder = divmod(residual, prime)
            if remainder:
                break
            residual = quotient
            divisions += 1

    candidate_sum = source // residual
    factor, square_tests = balanced_factor_from_sum(n, candidate_sum)
    return dict(prime_limit=prime_limit, inverse_gap=inverse_gap, smooth_part=str(candidate_sum),
                residual_bits=residual.bit_length(), divisions=divisions,
                remainder_checks=checks, square_tests=square_tests, factor=factor)
