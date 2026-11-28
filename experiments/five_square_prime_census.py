"""Complete small-width prime-pair censuses for product one at five prime squares."""

from collections import Counter
from math import isqrt, prod

if __package__:
    from .gap_coverage import primes_through
else:
    from gap_coverage import primes_through

PRIMES = (5, 7, 11, 13, 17)
MODULUS = prod(p**2 for p in PRIMES)


def census(bits):
    lo = 1 << (bits - 1)
    hi = 1 << bits
    candidates = {p for p in primes_through(hi - 1) if p >= lo}
    rows = []
    for p in sorted(candidates):
        first = pow(p, -1, MODULUS)
        for q in range(first, hi, MODULUS):
            if q <= p or q not in candidates or (p * q).bit_length() != 2 * bits:
                continue
            weight = prod(r if (p - q) % r == 0 else 2 for r in PRIMES)
            steps = (p + q) // 2 - isqrt(p * q - 1)
            rows.append((p, q, weight, steps))
    return rows


if __name__ == '__main__':
    for bits in (22, 23, 24):
        rows = census(bits)
        buckets = Counter(weight for _, _, weight, _ in rows)
        print(f'{bits}-bit primes: {len(rows)} qualifying products, weights {dict(sorted(buckets.items()))}')
        if rows:
            print('Fewest midpoints:', min(rows, key=lambda row: row[3]))
