"""Count positive representations recognized from a fourth-power remainder.

Replay the bounded census with python3 -m experiments.quartic_product_strips.
"""

from math import isqrt

from experiments.local_midpoint_lanes import is_prime


def fourth_root(n):
    return isqrt(isqrt(n))


def recognize(n):
    x = fourth_root(n)
    residual = n - x**4
    y = fourth_root(residual // 4)
    if x == 0 or y == 0 or residual != 4*y**4:
        return None
    midpoint = x*x + 2*y*y
    gap = 2*x*y
    return midpoint - gap, midpoint + gap


def census(limit):
    products = set()
    primes = balanced = 0
    for x in range(1, fourth_root(limit) + 1, 2):
        cap = min(limit, (x+1)**4 - 1)
        last_y = fourth_root((cap - x**4) // 4)
        for y in range(1, last_y + 1):
            n = x**4 + 4*y**4
            pair = recognize(n)
            assert n not in products and pair is not None
            p, q = pair
            assert p*q == n and p+q == 2*x*x + 4*y*y
            products.add(n)
            if is_prime(p) and is_prime(q):
                primes += 1
                bits = p.bit_length()
                balanced += bits == q.bit_length() and n.bit_length() == 2*bits
    if limit <= 2**16:
        direct = {n for n in range(1, limit+1, 2) if recognize(n) is not None}
        assert products == direct
    return len(products), primes, balanced


if __name__ == "__main__":
    for bits, expected in [(16, 35), (24, 403), (32, 4636)]:
        counts = census(2**bits)
        assert counts[0] == expected
        print(f"Up to 2^{bits}: {counts[0]} odd inputs, {counts[1]} prime pairs, "
              f"{counts[2]} equal-width prime pairs with a full-width product.")
    n = 151847041
    p, q = recognize(n)
    assert is_prime(p) and is_prime(q) and (p, q) == (10301, 14741)
    rank = (p+q)//2 - isqrt(n-1)
    assert rank == 199
    print(f"{n} = {p} × {q}, ordinary Fermat rank {rank}.")
    miss = 1065**4 + 4*187**4
    assert miss == 805853*1602473 and fourth_root(miss) == 1066 and recognize(miss) is None
    print(f"{miss} falls outside the strip for x = 1065.")
