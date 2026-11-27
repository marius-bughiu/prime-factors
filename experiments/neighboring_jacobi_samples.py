"""Enumerate the three-sign distribution on small odd levels using only the product."""
import argparse
import json
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import isqrt
from pathlib import Path

from experiments.projective_word_moments import jacobi


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/neighboring-jacobi-samples.json'
PAIRS = tuple(product((-1, 1), repeat=2))
TRIPLES = tuple(product((-1, 1), repeat=3))
PARITY_TRIPLES = tuple((u, v, u*v) for u, v in PAIRS)


def distance(counts, n, reference):
    mass = Fraction(1, len(reference))
    return 1 - sum(min(Fraction(counts[value], n), mass) for value in reference)


def measure(n):
    if n < 3 or n > 10000 or n % 2 == 0:
        raise ValueError('Choose an odd toy modulus between 3 and 10000.')
    sign = [jacobi(t*t - 4, n) for t in range(n)]
    pairs = Counter((sign[t], sign[(t+4) % n]) for t in range(n))
    triples = Counter((sign[(2*s-2) % n], sign[(2*s+2) % n], sign[s]) for s in range(n))
    if any(u*v*w < 0 for u, v, w in triples):
        raise ArithmeticError('Negative triple product')
    if any(triples[u, v, u*v] != pairs[u, v] for u, v in PAIRS):
        raise ArithmeticError('A nonzero pair did not extend to its parity triple')

    prime_sum = pairs[0, 0] - 1
    discriminant = prime_sum**2 - 4*n
    gap = isqrt(discriminant) if discriminant >= 0 else None
    factors = []
    if gap is not None and gap**2 == discriminant and (prime_sum-gap) % 2 == 0:
        p, q = (prime_sum-gap)//2, (prime_sum+gap)//2
        if 1 < p <= q and p*q == n:
            factors = [str(p), str(q)]
    return dict(n=str(n), factors=factors, nonzero_pair_counts=[pairs[key] for key in PAIRS],
                both_zero=pairs[0, 0], pair_distance=str(distance(pairs, n, PAIRS)),
                triple_distance=str(distance(triples, n, TRIPLES)),
                parity_distance=str(distance(triples, n, PARITY_TRIPLES)),
                jacobi_evaluations=n, pair_rows=n, triple_rows=n,
                recovery_square_roots=int(gap is not None))


def check_model(row, p, q):
    n = p*q
    a = (p-3)*(q-3)
    b = (1+jacobi(2, p))*(1+jacobi(2, q))
    c = (1+jacobi(-1, p))*(1+jacobi(-1, q))
    assert row['n'] == str(n) and row['factors'] == [str(p), str(q)]
    assert row['both_zero'] == p+q+1
    for (u, v), count in zip(PAIRS, row['nonzero_pair_counts']):
        assert 4*count == a+(u+v)*b+u*v*c
    assert Fraction(row['triple_distance']) >= Fraction(1, 2)
    if p >= 5:
        assert Fraction(row['pair_distance']) == Fraction(n-a, n)
        assert row['parity_distance'] == row['pair_distance']
    if p >= 13:
        assert row['triple_distance'] == '1/2'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exhaustive', action='store_true',
                        help='Also test all distinct odd primes through 97.')
    args = parser.parse_args()
    for case in json.loads(FIXTURE.read_text()):
        row = measure(int(case['n']))
        check_model(row, *map(int, case['expected_factors']))
        for name in ('nonzero_pair_counts', 'both_zero', 'pair_distance', 'triple_distance'):
            assert row[name] == case[name]
        print(json.dumps(row, sort_keys=True))
    if args.exhaustive:
        primes = [p for p in range(3, 98, 2) if all(p % d for d in range(2, isqrt(p)+1))]
        cases = residues = 0
        for p, q in combinations(primes, 2):
            check_model(measure(p*q), p, q)
            cases += 1
            residues += p*q
        print(f'{cases} odd prime pairs, {residues} residues over all levels')


if __name__ == '__main__':
    main()
