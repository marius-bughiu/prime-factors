"""Bounded cross-check of balanced representative pairs and signed product lifts."""

import json
from collections import Counter
from math import isqrt
from pathlib import Path


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/fractional-matched-divisors.json'


def direct_pairs(n, m):
    """Check the original conditions via all possible ordinary sums and smaller entries."""
    smallest_sum = isqrt(4*n-1)+1
    largest_sum = isqrt((9*n-1)//2)
    return {(x, s-x) for s in range(smallest_sum, largest_sum+1)
            for x in range(2, s//2+1)
            if s-x < min(m, 2*x) and x*(s-x) % m == n % m}


def divisor_pairs(n, m):
    """Enumerate the exact signed interval and divisors up to each lift's square root."""
    first = -((n-1)//(9*m))
    last = (n-1)//(8*m)
    hits = {}
    for j in range(first, last+1):
        product = n+j*m
        for x in range(2, isqrt(product)+1):
            y, remainder = divmod(product, x)
            if remainder == 0 and y < m and y < 2*x and 4*n <= (x+y)**2 and 2*(x+y)**2 < 9*n:
                hits[x, y] = j
    return first, last, hits


def check(n, m):
    first, last, hits = divisor_pairs(n, m)
    if direct_pairs(n, m) != set(hits):
        raise ArithmeticError(f'Divisor and ordinary-sum enumerations disagree at {n}, {m}')
    counts = Counter(x+y for x, y in hits)
    return dict(product=n, modulus=m, index_range=[first, last],
                pairs=[dict(x=x, y=y, index=j, lifted_product=x*y)
                       for (x, y), j in sorted(hits.items())],
                sum_multiplicities=[[s, count] for s, count in sorted(counts.items())])


def study():
    totals = Counter()
    for n in range(1, 97):
        for m in range(1, 33):
            row = check(n, m)
            totals['cases'] += 1
            totals['pairs'] += len(row['pairs'])
            totals['distinct_sums_per_case'] += len(row['sum_multiplicities'])
    controls = [check(851, 49), check(2021, 70), check(583201, 72898)]
    if controls[0]['sum_multiplicities'] != [[60, 2], [61, 1]]:
        raise ArithmeticError('The repeated sum at 851 or the two sums on lift 900 are missing')
    if (583201-8*72898 != 17 or 809*811 != 583201+72898 or
            controls[-1]['sum_multiplicities'] != [[1550, 1], [1620, 1]]):
        raise ArithmeticError('The sharp-17 control failed')
    return dict(scope='All 1 ≤ N ≤ 96 and 1 ≤ m ≤ 32, and three explicit larger controls.',
                totals=dict(totals), controls=controls)


if __name__ == '__main__':
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Matched divisor results differ from the reviewed fixture')
    print(f"Verified {result['totals']['cases']} small cases and {len(result['controls'])} controls.")
