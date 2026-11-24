"""Certify single-row and cross-row bounds for smooth fractions.

Run directly with Python 3.9 or later. All numerical operations are on integers
or rational numbers. The two certificates use different bounds on prime sizes.
"""

from fractions import Fraction
from math import isqrt, lcm, prod


SMALL_LIMIT = 1 << 16
TERMS = 16
COMMON = lcm(*range(1, TERMS + 2))
LOG2_LOWER = sum(Fraction(2, k * 3**k) for k in range(1, 16, 2))


def small_primes():
    sieve = bytearray([1]) * (SMALL_LIMIT + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(SMALL_LIMIT) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((SMALL_LIMIT - p*p) // p + 1)
    return [p for p in range(2, SMALL_LIMIT + 1) if sieve[p]]


def log_lower(x):
    """Lower-bound ln(x) for x >= 1 using binary reduction and eight atanh terms."""
    x = Fraction(x)
    assert x >= 1
    k = (x.numerator // x.denominator).bit_length() - 1
    y = x / (1 << k)
    z = (y - 1) / (y + 1)
    value = k * LOG2_LOWER + sum(2 * z**i / i for i in range(1, 16, 2))
    return Fraction((value * (1 << 24)) // 1, 1 << 24)


def rank_bins(primes, capacity):
    """A lower prime value and the number of indices it covers."""
    bins = [(p, 1) for p in primes]
    start = len(primes) + 1
    while start <= capacity:
        step = 1 << max(0, start.bit_length() - 1 - 8)
        stop = min(capacity + 1, (start // step + 1) * step)
        log_start = log_lower(start)
        lower = (start * (log_start + log_lower(log_start) - 1)) // 1
        bins.append((lower, stop - start))
        start = stop
    return bins


def binomial_bins(primes, capacity):
    """Fill dyadic intervals to their elementary binomial-coefficient capacities."""
    bins = [(p, 1) for p in primes]
    left = capacity - len(primes)
    j = SMALL_LIMIT.bit_length() - 1
    while left:
        count = min(left, (1 << (j + 1)) // j)
        bins.append((1 << j, count))
        left -= count
        j += 1
    return bins


def log_factor_upper(prime_lower, sigma, scale):
    """Return an integer at least scale times -ln(1 - prime_lower**(-sigma))."""
    a, d = sigma.numerator, sigma.denominator
    assert d > 0 and d & (d - 1) == 0
    # Work with 64 extra bits. Every division and square root rounds upward.
    precision = scale << 64
    root = -(-precision // prime_lower)
    for _ in range(d.bit_length() - 1):
        root = 1 + isqrt(root * precision - 1)
    power = precision
    while a:
        if a % 2:
            power = -(-(power * root) // precision)
        root = -(-(root * root) // precision)
        a //= 2
    q = -(-power // (1 << 64))
    assert q < scale
    # Sum z^k/k exactly with z=q/scale and bound its tail by z^(m+1)/((m+1)(1-z)).
    partial = sum((COMMON // k) * q**k * scale**(TERMS-k) for k in range(1, TERMS+1))
    numerator = partial * (scale - q) + (COMMON // (TERMS + 1)) * q**(TERMS + 1)
    denominator = COMMON * scale**(TERMS-1) * (scale - q)
    return -(-numerator // denominator)


def certify(bins, sigma, capacity, scale):
    assert sum(count for _, count in bins) == capacity
    euler = sum(count * log_factor_upper(p, sigma, scale) for p, count in bins)
    bits = 3 - 2047 + 2046 * sigma + 2 * Fraction(euler, scale) / LOG2_LOWER + Fraction(1, 1024)
    return euler, bits


def square_tail_bits(sigma, capacity):
    """Upper bound for two copies of the extra log2 mass from unlisted prime squares."""
    delta = 2 * sigma - 1
    n, d = delta.numerator, delta.denominator
    assert n > 0
    # Certify 2 K^(-delta) / delta < 2^-26 by raising to the d-th power.
    assert ((1 << 27) * d)**d < n**d * capacity**n
    assert LOG2_LOWER > Fraction(1, 2)
    return Fraction(1, 1 << 24)


def main():
    primes = small_primes()
    assert len(primes) == 6542
    assert primes[255] == 1619 and prod(primes[:256]).bit_length() == 2290
    others = (1 << 48) - 1
    assert (1 << 40) + 255 * others < 1 << 56
    assert (1 << 40) + 4100 * 255 * others < 1 << 68
    for k, places, label, build, sigma, millibits in (
        (40, 64, "Dusart", rank_bins, Fraction(109, 128), 208299),
        (40, 64, "binomial", binomial_bins, Fraction(223, 256), 157324),
        (56, 128, "Dusart", rank_bins, Fraction(921, 1024), 128284),
        (56, 128, "binomial", binomial_bins, Fraction(235, 256), 86384),
        (68, 128, "Dusart", rank_bins, Fraction(943, 1024), 94357),
        (68, 128, "binomial", binomial_bins, Fraction(15, 16), 57391),
    ):
        capacity, scale = 1 << k, 1 << places
        numerator, bits = certify(build(primes, capacity), sigma, capacity, scale)
        adjusted = bits + square_tail_bits(sigma, capacity)
        assert adjusted < -Fraction(millibits, 1000)
        saving = (-adjusted) // 1
        print(f"K=2^{k} {label}: sigma={sigma}, ln(Z) <= {numerator}/2^{places}, "
              f"including square factors: one source < 2^-{saving}, "
              f"2^48 sources < 2^-{saving-48}", flush=True)


if __name__ == "__main__":
    main()
