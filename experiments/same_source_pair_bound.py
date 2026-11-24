"""Certify the frequency bound for two distinct dependent fractions of one unit residue."""

from collections import defaultdict
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt


def divisor_constant(a, d):
    """Return the rational d-th power of sup_n tau(n^2)/n^(a/d)."""
    cutoff = 2
    while cutoff**a < 3**d:
        cutoff *= 2
    sieve = bytearray([1]) * (cutoff + 1)
    for p in range(2, isqrt(cutoff) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((cutoff - p*p)//p + 1)
    numerator, denominator, active = 1, 1, 0
    for p in range(2, cutoff + 1):
        if not sieve[p]:
            continue
        step = p**a
        exponent = 0
        while (2*exponent+3)**d > (2*exponent+1)**d * step:
            exponent += 1
        if exponent:
            numerator *= (2*exponent+1)**d
            denominator *= step**exponent
            active += 1
    return Fraction(numerator, denominator), active


def ceil_log2_ratio(ratio):
    """Least k with a positive ratio at most 2^k."""
    a, b = ratio.numerator, ratio.denominator
    k = a.bit_length() - b.bit_length()
    above = a > b << k if k >= 0 else a << -k > b
    return k + int(above)


def probability_bound():
    a, d = 171, 1024
    assert 4*(d-a) >= 3*d and 5**4 < 8*3**4  # 2^(-t) < 3/5 for t >= 3/4
    assert Fraction(256, 255)**2 < Fraction(101, 100)
    h = Fraction(7, 10)
    assert 1 + h + h*h/2 + h**3/6 > 2 and 1+1024*h < 718
    constant, active = divisor_constant(a, d)
    # Four roots, two numerator signs, two chains and the determinant's factor 1/2
    # are included in 16; 5/2 bounds the remaining geometric series.
    prefactor = 16 * Fraction(101, 100) * 718 * Fraction(5, 2)
    twice_d_log = ceil_log2_ratio((prefactor**d * constant)**2)
    saved = Fraction(2045*(d-a) - twice_d_log, 2*d)
    assert saved > 796
    return active, saved


def small_example():
    """Directly enumerate every eligible fraction at a small composite modulus."""
    n = 437
    rows = defaultdict(list)
    for b in range(1, (n+1)//2):
        if gcd(b, n) != 1:
            continue
        inverse = pow(b, -1, n)
        for a in range(1, (n-1)//(2*b)+1):
            if gcd(a, b*n) != 1:
                continue
            for sign in (1, -1):
                rows[(sign*a*inverse) % n].append((sign*a*b, b))
    good = set()
    for residue, candidates in rows.items():
        for (first, b), (second, d) in combinations(candidates, 2):
            product = first * second
            if product > 0 and isqrt(product)**2 == product:
                factor = gcd(residue*b*d - isqrt(product), n)
                assert 1 < factor < n
                good.add(residue)
    assert pow(60, 2, n) in good
    squares = sum(x*x % n in good for x in range(1, n) if gcd(x, n) == 1)
    return len(good), squares


if __name__ == "__main__":
    count, square_count = small_example()
    print(f"N=437: {count} eligible unit residues, {square_count} eligible unit-square inputs")
    active, saved = probability_bound()
    k = saved // 1
    print(f"{active} active primes; certified square-input saving >= {saved} bits")
    print(f"one draw: square < 2^-{k}, unit < 2^-{k+2}")
    print(f"2^48 draws: square < 2^-{k-48}, unit < 2^-{k+2-48}")
