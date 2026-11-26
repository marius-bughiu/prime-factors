"""Check the predeclared high-square-root-remainder prediction.

Reproduce the full published counts from the repository root with
    python3 -m experiments.sqrt_remainder_census | diff - research/sqrt-remainder-census.json
"""

from bisect import bisect_left, bisect_right
from functools import cache
from hashlib import shake_256
import json
from math import gcd, isqrt, prod

from scripts.factor import primes_through


SEED = b'sqrt-remainder-inner-postdesign-v1'


def high_remainder(n):
    """Exactly (n - r²)/(2r + 1) > 1/2 with r = floor(sqrt(n))."""
    r = isqrt(n)
    return n - r * r > r


def result(bits, counts):
    return dict(factor_bits=bits, pairs=sum(counts), correct=counts[0] + counts[3],
                counts=counts)


def exhaustive(bits):
    """Count each eligible unordered pair once, ordered low/outer through high/inner."""
    bound = 1 << bits
    primes = [p for p in primes_through(bound - 1) if p >= bound // 2]
    cubes = [p**3 for p in primes]
    cutoff = bound**2 // 2
    counts = [0] * 4
    for i, p in enumerate(primes):
        # Full-width eligibility and q³ <= B²p split the sorted q-list into two runs.
        first = bisect_left(primes, (cutoff + p - 1) // p, lo=i + 1)
        middle = bisect_right(cubes, bound**2 * p, lo=first)
        for start, stop, inner in ((first, middle, 1), (middle, len(primes), 0)):
            high = sum(high_remainder(p * q) for q in primes[start:stop])
            counts[inner] += stop - start - high
            counts[2 + inner] += high
    return result(bits, counts)


@cache
def trial_primorial():
    # Every composite 32-bit candidate has a prime divisor at most 65,535.
    return prod(primes_through(65_535))


def draw_prime(side, index):
    prefix = SEED + b'\0' + side + index.to_bytes(8, 'big')
    retry = 0
    while True:
        digest = shake_256(prefix + retry.to_bytes(8, 'big')).digest(4)
        p = int.from_bytes(digest, 'big') | (1 << 31) | 1
        # The Fermat check skips costly gcds. The gcd proves primality exactly here.
        if pow(2, p - 1, p) == 1 and gcd(p, trial_primorial()) == 1:
            return p
        retry += 1


def fresh_panel(count):
    counts = [0] * 4
    index = accepted = 0
    while accepted < count:
        p, q = sorted(draw_prime(side, index) for side in (b'p', b'q'))
        index += 1
        n = p * q
        if p == q or n < (1 << 63):
            continue
        inner = q**3 <= (p << 64)
        counts[2 * high_remainder(n) + inner] += 1
        accepted += 1
    return dict(**result(32, counts), draw_indices=index)


def report():
    return dict(
        reproduce='python3 -m experiments.sqrt_remainder_census | diff - research/sqrt-remainder-census.json',
        population='p < q, both b-bit primes, p*q >= 2^(2b-1).',
        prediction='Predict inner when N - floor(sqrt(N))^2 > floor(sqrt(N)).',
        inner='q^3 <= 2^(2b) * p',
        counts_order=['low_outer', 'low_inner', 'high_outer', 'high_inner'],
        seed=SEED.decode(),
        sampler='For index 0 onward and sides ASCII p,q, hash seed || NUL || side || '
                'index_u64be || retry_u64be with SHAKE256. Read 4 bytes big-endian, '
                'set the high and low bits, and take the first prime for each side '
                'starting at retry 0. Sort each pair, keep eligible draws in order '
                'with replacement, and stop after 65,536 accepted pairs.',
        primality='Small primes by Eratosthenes sieve. Sampled 32-bit candidates by '
                  'exact coprimality with the product of all primes through 65,535. '
                  'The factors are generated for evaluation. No individual Lean '
                  'factorization certificates are produced by this census.',
        exhaustive=[exhaustive(bits) for bits in range(5, 19)],
        sample=fresh_panel(65_536),
    )


if __name__ == '__main__':
    print(json.dumps(report(), indent=2))
