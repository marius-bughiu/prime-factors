"""Bracket the number of even 1,025-bit sums supported on primes through 31."""

from experiments.gap_coverage import primes_through
from experiments.neighbor_smooth_sum import balanced_factor_from_sum


def smooth_sum_bounds(factor_bits=1024, prime_limit=31, precision=256):
    """Each odd part below 2**factor_bits lifts to exactly one even sum in the band."""
    if factor_bits < 1 or prime_limit < 2 or precision < 1:
        raise ValueError("need positive bit width and precision and a prime cutoff of at least two")
    primes = [p for p in primes_through(prime_limit) if p != 2]
    lower_weights = [(p**precision).bit_length()-1 for p in primes]
    capacity = factor_bits * precision - 1

    def count(weights):
        coefficients = [0] * (capacity+1)
        coefficients[0] = 1
        for weight in weights:
            for index in range(weight, capacity+1):
                coefficients[index] += coefficients[index-weight]
        return sum(coefficients)

    return count([w+1 for w in lower_weights]), count(lower_weights)


def scan_two_three(n):
    """Check every possible sum 2**a * 3**b for two odd factor_bits-bit factors."""
    if n < 5 or n % 2 == 0:
        raise ValueError("need a positive odd product of at least five")
    factor_bits = (n.bit_length()+1)//2
    lower_sum = 1 << factor_bits
    excludes_power_of_two = 4*n > lower_sum**2
    if n % 3 == 1 and excludes_power_of_two:
        return dict(factor_bits=factor_bits, remainder_mod_three=1, excluded_by_remainder_and_size=True,
                    exponents_visited=0, square_tests=0, winning_exponent=None, factor=None)
    odd_part = 1
    exponent = visited = square_tests = 0
    while odd_part < lower_sum:
        shift = factor_bits + 1 - odd_part.bit_length()
        candidate_sum = odd_part << shift
        factor, tests = balanced_factor_from_sum(n, candidate_sum)
        square_tests += tests
        visited += 1
        if factor is not None:
            return dict(factor_bits=factor_bits, remainder_mod_three=n % 3, excluded_by_remainder_and_size=False,
                        exponents_visited=visited, square_tests=square_tests,
                        winning_exponent=exponent, factor=factor)
        exponent += 1
        odd_part *= 3
    return dict(factor_bits=factor_bits, remainder_mod_three=n % 3, excluded_by_remainder_and_size=False,
                exponents_visited=visited, square_tests=square_tests,
                winning_exponent=None, factor=None)


if __name__ == '__main__':
    low, high = smooth_sum_bounds()
    print(f'Number of even 1,025-bit sums with prime divisors through 31: [{low}, {high}]')
    print(f'Population count inequality verified: {44331 * high * 2**947 < 2**1023}')
