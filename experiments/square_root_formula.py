"""Compare public square-root formulas after the same nine-position check.

Every full-width product from an unordered pair of distinct b-bit primes is
included. The source labels generate the population; readings() sees only n.
"""
from itertools import combinations
from math import gcd, isqrt, prod

from experiments.block_subresultant import probe
from scripts.factor import primes_through


def readings_at(n,t):
    gap = n-t*t
    return {
        'adjacent': gcd(n,t-5),
        'fixed_quartic': probe(n,3,t),
        'reciprocal_quartic': gcd(n,gap*gap-22*gap+1),
        'remainder_width': probe(n,2*gap+3,t),
    }


def readings(n):
    return readings_at(n,isqrt(n))


def census(bits):
    lower = 1 << (bits-1)
    primes = [p for p in primes_through(2*lower-1) if p >= lower]
    names = ('adjacent','fixed_quartic','reciprocal_quartic','remainder_width')
    counts = dict.fromkeys(names,0)
    exclusive = counts.copy()
    whole = counts.copy()
    eligible = misses = 0
    for p,q in combinations(primes,2):
        n = p*q
        if n.bit_length() != 2*bits:
            continue
        eligible += 1
        t = isqrt(n)
        if gcd(n,prod(range(t-4,t+5))) != 1:
            continue
        misses += 1
        hits = []
        for name, divisor in readings(n).items():
            if 1 < divisor < n:
                assert divisor in (p,q)
                counts[name] += 1
                hits.append(name)
            elif divisor == n:
                whole[name] += 1
        if len(hits) == 1:
            exclusive[hits[0]] += 1
    return dict(bits=bits,eligible=eligible,misses=misses,splits=counts,
                exclusive=exclusive,whole_gcds=whole)


if __name__ == '__main__':
    for width in (9,10,11,12,13):
        print(census(width))
