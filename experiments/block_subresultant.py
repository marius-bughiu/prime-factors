"""Compare one extra Euclidean pivot with one adjacent trial after a nine-position miss."""

from itertools import combinations
from math import gcd, isqrt, prod


def probe(n, width, shift):
    """Return the normalized quartic gcd using only the product, width and shift."""
    if n < 2 or width < 3 or width % 2 == 0:
        raise ValueError("expected n >= 2 and odd width >= 3")
    m2 = width * width % n
    y = shift * shift % n
    value = ((48 * y - 24 * (1 + m2)) * y + pow(m2 - 1, 3, n)) % n
    return gcd(n, value)


def search(n):
    """Test one 3×3 rectangle, then one pivot and one comparison on a unit rectangle."""
    t = isqrt(n)
    if t < 5:
        raise ValueError("the nine-position block requires a center of at least five")
    rectangle = gcd(n, prod(range(t - 4, t + 5)))
    work = dict(center=str(t), width=3, rectangle_positions=9, square_roots=1,
                rectangle_gcds=1, pivot_gcds=0, adjacent_gcds=0,
                rectangle_gcd=str(rectangle), pivot_gcd=None, adjacent_gcd=None)
    if rectangle != 1:
        divisor = rectangle if rectangle < n else None
        return divisor, dict(work, outcome="rectangle_divisor" if divisor else "whole_product")

    pivot = probe(n, 3, t)
    adjacent = gcd(n, t - 5)
    work.update(pivot_gcd=str(pivot), adjacent_gcd=str(adjacent), pivot_gcds=1, adjacent_gcds=1)
    if 1 < pivot < n:
        return pivot, dict(work, outcome="pivot_divisor")
    if 1 < adjacent < n:
        return adjacent, dict(work, outcome="adjacent_divisor")
    return None, dict(work, outcome="no_split")


def compare(n):
    """Give the adjacent comparison the same shift and the same unrevealing rectangles."""
    _, work = search(n)
    return tuple(None if work[key] is None else int(work[key])
                 for key in ("rectangle_gcd", "pivot_gcd", "adjacent_gcd"))


def census(bits):
    primes = [p for p in range(2 ** (bits - 1), 2 ** bits)
              if all(p % d for d in range(2, isqrt(p) + 1))]
    pairs = hits = negative = quartic = adjacent = both = whole = 0
    for p, q in combinations(primes, 2):
        n = p * q
        if n.bit_length() != 2 * bits:
            continue
        pairs += 1
        original, a, b = compare(n)
        if original != 1:
            hits += 1 < original < n
            whole += original == n
            continue
        negative += 1
        quartic += 1 < a < n
        adjacent += 1 < b < n
        both += 1 < a < n and 1 < b < n
    return pairs, hits, whole, negative, quartic, adjacent, both


if __name__ == "__main__":
    print("prime_bits pairs original_splits whole_product negative extra_quartic extra_adjacent both")
    for prime_bits in (9, 10, 11):
        print(prime_bits, *census(prime_bits))
