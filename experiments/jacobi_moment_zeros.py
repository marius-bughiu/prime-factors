"""Compare raw even Jacobi moments with the prime-component zero criterion on tiny products."""

import argparse
import json
from math import comb, gcd, isqrt
from pathlib import Path

from experiments.jacobi_middle_degree import moment
from experiments.projective_word_moments import jacobi


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-moment-zeros.json'


def measure(n, degrees):
    """The direct sum uses only the product and degrees; each degree visits all n residues."""
    if not 3 <= n <= 255 or n % 2 == 0:
        raise ValueError('the controls require a positive odd product between 3 and 255')
    if not degrees or any(k <= 0 or k % 2 for k in degrees):
        raise ValueError('each degree must be positive and even')
    signs = [jacobi(x*x-4, n) for x in range(n)]
    moments = [moment(n, k, signs) for k in degrees]
    return dict(moments=moments, gcds=[gcd(n, value) for value in moments],
                jacobi_signs=n, residue_powers=n*len(degrees), gcd_checks=len(degrees))


def check_criterion(n, degrees, measured, factors):
    """Use the supplied factors only to validate the independently computed moments."""
    p, q = map(int, factors)
    assert p*q == n and 2 < p < q
    assert all(all(prime % d for d in range(2, isqrt(prime)+1)) for prime in (p, q))
    for k, value, observed in zip(degrees, measured['moments'], measured['gcds']):
        predicted = 1
        for prime in (p, q):
            r = k % (prime-1)
            local = comb(r, r//2) if r else 1 + (-1)**((prime-1)//2)
            assert value % prime == local % prime, (n, k, prime, value, local)
            if prime % 4 == 3 and r == 0:
                predicted *= prime
        assert observed == predicted, (n, k, observed, predicted)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='compare the direct calculations with the fixture')
    args = parser.parse_args()
    for case in json.loads(FIXTURE.read_text()):
        n = int(case['n'])
        degrees = case['degrees']
        measured = measure(n, degrees)
        check_criterion(n, degrees, measured, case['factors'])
        if args.check:
            assert measured == case['observed'], (n, measured)
        print(json.dumps(dict(n=n, degrees=degrees, **measured)))


if __name__ == '__main__':
    main()
