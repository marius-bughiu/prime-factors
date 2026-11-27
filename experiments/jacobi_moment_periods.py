"""Measure the periods of complete Jacobi moments and compare with unit orders on small inputs."""

import json
from math import gcd, lcm
from pathlib import Path

from experiments.projective_word_moments import jacobi


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-moment-periods.json'


def first_repeating_shift(values, length):
    """Compare a full block against each shift through the given bound on the period."""
    block = values[:length]
    for shift in range(1, length + 1):
        if values[shift:shift + length] == block:
            return shift
    raise ValueError('no period found within the block')


def unit_exponent(n):
    """Independently measure each unit's order by repeated modular multiplication."""
    exponent = 1
    for base in range(1, n):
        if gcd(base, n) != 1:
            continue
        power = 1
        for order in range(1, n + 1):
            power = power * base % n
            if power == 1:
                exponent = lcm(exponent, order)
                break
        else:
            raise ArithmeticError('unit order exceeded the size of the residue ring')
    return exponent


def measure(n):
    """Sum all residues at successive positive degrees for a product of two distinct odd primes."""
    terms = [jacobi(t*t - 4, n) for t in range(n)]
    moments = []
    for _ in range(4*n):
        terms = [t*value % n for t, value in enumerate(terms)]
        moments.append(sum(terms) % n)
    return dict(positive_period=first_repeating_shift(moments, n),
                even_period=first_repeating_shift(moments[1::2], n),
                unit_exponent=unit_exponent(n), degrees=len(moments),
                jacobi_signs=n, weighted_term_updates=n*len(moments))


def main():
    for case in json.loads(FIXTURE.read_text()):
        n = int(case['n'])
        result = measure(n)
        for key in ('positive_period', 'even_period', 'unit_exponent'):
            assert result[key] == case[key], (n, key, result[key])
        p, q = map(int, case['factors'])
        assert p*q == n and result['unit_exponent'] == lcm(p-1, q-1)
        periods = [1 if prime == 5 else (prime-1)//2 for prime in (p, q)]
        assert result['even_period'] == lcm(*periods)
        print(json.dumps(dict(n=n, **result)))


if __name__ == '__main__':
    main()
