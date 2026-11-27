"""Evaluate the public middle-degree Jacobi discrepancy on small balanced semiprimes."""

import json
from math import comb, gcd, isqrt
from pathlib import Path

from experiments.projective_word_moments import jacobi


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-middle-degree.json'


def moment(n, degree, signs):
    return sum(pow(t, degree, n)*sign for t, sign in enumerate(signs)) % n


def measure(n):
    k = 2*(isqrt(n)//2)
    coefficient = comb(k, k//2)
    signs = [jacobi(t*t-4, n) for t in range(n)]
    observed = moment(n, k, signs)
    difference = (observed - coefficient) % n
    larger = gcd(n, difference)

    successor_root = isqrt(n+1)
    twins = successor_root**2 == n+1
    coefficient_gcd = gcd(n, coefficient)
    smaller = successor_root-1 if twins else coefficient_gcd
    assert 1 < smaller < larger and smaller*larger == n
    # Once both factors have been recovered, verify each additional even degree
    # of the full interval against its direct sum, reusing the N Jacobi signs.
    other_degrees = [r for r in range(smaller-1, larger-1, 2) if r != k]
    for r in other_degrees:
        value = moment(n, r, signs)
        assert gcd(n, value - comb(r, r//2)) == larger
    return dict(n=n, degree=k, moment=observed, central=coefficient, discrepancy=difference,
                larger=larger, coefficient_gcd=coefficient_gcd, twin_square=twins, smaller=smaller,
                jacobi_signs=n, public_degree_terms=n, additional_interval_terms=n*len(other_degrees))


def main():
    for case in json.loads(FIXTURE.read_text()):
        result = measure(int(case['n']))
        assert list(map(int, case['factors'])) == [result['smaller'], result['larger']]
        for key in ('degree', 'moment', 'central', 'discrepancy', 'coefficient_gcd', 'twin_square'):
            assert result[key] == case[key], (result['n'], key, result[key])
        print(json.dumps(result))


if __name__ == '__main__':
    main()
