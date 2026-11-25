"""Exhaustively fit one signed factor remainder per modular transcript at 11 bits."""

from collections import Counter, defaultdict
from itertools import combinations
from math import lcm

from scripts.factor import primes_through


def census(budget: int) -> tuple[int, ...]:
    x = radix = 1024
    primes = [p for p in primes_through(2*x-1) if p >= x]
    choices = primes_through(budget//3)
    first, second = choices[-1], choices[-2]
    leaves = defaultdict(Counter)
    pairs = 0
    for p, q in combinations(primes, 2):
        n = p*q
        if n < 2*x*x:
            continue
        modulus = 3*(first if n % 3 == 1 else second)
        labels = {min(v % radix, (-v) % radix) for v in (p, q)}
        leaves[modulus, n % modulus].update(labels)
        pairs += 1
    hits = sum(max(histogram.values()) for histogram in leaves.values())
    return budget, first, second, lcm(3*first, 3*second), len(leaves), hits, pairs


if __name__ == "__main__":
    print("budget first second global_lcm leaves hits pairs")
    for cap in (128, 512, 1024, 4096, 16384, 65536):
        print(*census(cap))
