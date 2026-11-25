"""Test the largest eligible multiplier at each public offset j=1,...,32."""

from collections import Counter
from hashlib import shake_256
from itertools import combinations
import json
from math import gcd, isqrt
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OFFSETS = 32


def sweep(n, last=OFFSETS):
    """Return the first factor and work over the entire specified schedule."""
    t = isqrt(n)
    h = n - t*t
    work = Counter()
    first = None
    for j in range(1, last+1):
        k = (j*t-1)//h if h else 0
        if k <= 0:
            continue
        work['eligible'] += 1
        scale = gcd(j, k)
        common = gcd(scale, n)
        if 1 < common < n:
            work['multiplier_gcd_hits'] += 1
            if first is None:
                first = (j, common)
            continue
        if scale > 1 and common == 1:
            work['duplicates'] += 1
            continue
        work['square_tests'] += 1
        d = j*j + 4*k*(t*j-h*k)
        root = isqrt(d)
        if root*root != d:
            continue
        if (root-j) % 2:
            raise ArithmeticError('unexpected square root parity')
        work['square_hits'] += 1
        m = (root-j)//2
        divisors = (gcd(k*t-m, n), gcd(k*t+m+j, n))
        proper = next((x for x in divisors if 1 < x < n), None)
        if proper is not None and first is None:
            first = j, proper
    return first, work


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def small_products(bits):
    primes = [x for x in range(2**(bits-1), 2**bits) if is_prime(x)]
    return [p*q for p,q in combinations(primes, 2) if (p*q).bit_length() == 2*bits]


def held_out_products(bits, count=128):
    """Build a separate fixed panel of balanced products for each width."""
    numbers = set()
    index = 0
    while len(numbers) < count:
        primes = []
        while len(primes) < 2:
            seed = f'grouped-offset-sweep-v1/{bits}/{index}'.encode()
            index += 1
            word = int.from_bytes(shake_256(seed).digest((bits+7)//8), 'big')
            n = word % 2**bits | 2**(bits-1) | 1
            if is_prime(n) and n not in primes:
                primes.append(n)
        product = primes[0]*primes[1]
        if product.bit_length() == 2*bits:
            numbers.add(product)
    return sorted(numbers)


def summarize(numbers):
    first_counts = Counter()
    totals = Counter()
    fermat_hits = common_hits = 0
    for n in numbers:
        t = isqrt(n-1)+1
        t += (t % 2) != (n % 4 == 1)
        ordinary = False
        for a in range(t, t+2*OFFSETS, 2):
            d = a*a-n
            root = isqrt(d)
            if root*root == d and a-root > 1:
                ordinary = True
                break
        fermat_hits += int(ordinary)
        first, work = sweep(n)
        totals.update(work)
        if first:
            common_hits += int(ordinary)
            j, divisor = first
            if n % divisor:
                raise ArithmeticError('incorrect divisor')
            first_counts[j] += 1
    return dict(inputs=len(numbers), hits_at_one=first_counts[1], hits_by_32=sum(first_counts.values()),
                first_offsets=dict(sorted(first_counts.items())), fermat_32=fermat_hits,
                common=common_hits, work=dict(totals))


def main():
    result = {f'census_{b}': summarize(small_products(b)) for b in (7, 8)}
    for b in (12, 16, 24):
        result[f'held_out_{b}'] = summarize(held_out_products(b))
    for row in json.loads((ROOT/'benchmarks/quartic-factor-lanes.json').read_text()):
        if row['id'] in ('unit-lane-crossed-2048', 'unit-lane-fresh-2048'):
            result[row['id']] = summarize([int(row['n'])])
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
