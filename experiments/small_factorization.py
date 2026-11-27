"""Factor small positive controls by trial division over the available primes."""

from math import isqrt

from scripts.factor import primes_through


def factor_small(value):
    if value < 1:
        raise ValueError('expected a positive integer')
    factors = {}
    for prime in primes_through(isqrt(value)):
        while value % prime == 0:
            factors[prime] = factors.get(prime, 0) + 1
            value //= prime
    if value > 1:
        factors[value] = 1
    return factors
