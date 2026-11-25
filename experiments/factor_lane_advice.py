"""Fit factor-remainder guesses to every labeled product at a small bit width."""

from collections import Counter, defaultdict
from itertools import combinations
from math import isqrt


def census(bits):
    modulus = 1 << bits
    x = modulus//2
    radix = 1 << (((5**5 << (10+6*(2*bits+1))).bit_length()+19)//20)
    primes = [p for p in range(x+1, modulus, 2) if all(p%d for d in range(3, isqrt(p)+1, 2))]
    counts = Counter()
    by_word = [defaultdict(Counter), defaultdict(Counter)]
    pairs = 0
    for p, q in combinations(primes, 2):
        n = p*q
        if n < modulus*x:
            continue
        labels = {min(a % radix, (-a) % radix) for a in (p, q)}
        high, low = divmod(n, modulus)
        counts.update(labels)
        by_word[0][high].update(labels)
        by_word[1][low].update(labels)
        pairs += 1

    def one_predicate(groups):
        # After a yes/no answer, at most two different guesses are possible.
        # For each word, training picks whichever of them covers more products.
        return max(sum(max(row[a], row[b]) for row in groups.values())
                   for a, b in combinations(counts, 2))

    return (bits, radix, pairs, max(counts.values()),
            max(map(one_predicate, by_word)),
            *(sum(max(row.values()) for row in groups.values()) for groups in by_word))


if __name__ == '__main__':
    for width in (8, 9, 10, 11):
        print(*census(width))
