"""Exhaustively assess omitted high product bits on bounded equal-width semiprimes."""
from math import isqrt


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def compare(width):
    bound = 1 << width
    k = (2 * width + 3) // 4
    mask = (1 << k) - 1
    exact = [0] * (bound * bound)
    for x in range(3, bound, 2):
        for y in range(x, bound, 2):
            exact[x * y] += y
    # Only now select semiprimes to check. The table includes every odd
    # nontrivial ordered input pair, including all composite factors.
    primes = [p for p in range(bound // 2, bound) if prime(p)]
    cases = [(p*q, q & mask) for i, p in enumerate(primes) for q in primes[i+1:]
             if (p*q).bit_length() == 2 * width]
    table = exact
    records = {}
    for bits in range(2 * width, width - 2, -1):
        matches = sum((table[n % len(table)] & mask) == expected for n, expected in cases)
        records[bits] = matches
        half = len(table) // 2
        table = [table[i] + table[i + half] for i in range(half)]
    if records[2 * width] != len(cases) or records[width - 1] != 0:
        raise AssertionError((width, cases, records))
    return len(cases), records


if __name__ == "__main__":
    for b in range(5, 11):
        pairs, hits = compare(b)
        print(f"factor bits={b}, pairs={pairs}, matches by retained product width={hits}")
