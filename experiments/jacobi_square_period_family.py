"""Split square-totient family controls at scale one, then check their periods using the factors."""

import json
from math import gcd
from pathlib import Path

from experiments.blum_signed_powers import prime_divisors
from experiments.predecessor_square import search


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-square-period-family.json'


def measure(n):
    split = search(n, 1)
    if split['factor'] is None:
        raise ValueError(f'The direct scale-one test did not split {n}')
    p, q = sorted((split['factor'], n//split['factor']))
    if p*q != n or not 7 <= p < q or prime_divisors(p) != (p,) or prime_divisors(q) != (q,):
        raise ValueError(f'The scale-one split of {n} did not yield two distinct primes ≥ 7')

    # With the recovered primes, the canonical period theorem gives this full
    # repeat length. Witnesses below independently rule out its maximal proper divisors.
    common = gcd(p-1, q-1)
    period = ((p-1)//common)*((q-1)//common)
    witnesses = []
    powers = 0
    for prime in prime_divisors(period):
        candidate = period//prime
        for base in range(2, 65):
            if gcd(base, n) != 1:
                continue
            powers += 1
            residue = pow(base, (n-1)*candidate, n)
            if residue != 1:
                witnesses.append(dict(prime=prime, candidate=candidate, base=base, residue=residue))
                break
        else:
            raise ValueError(f'No rejecting unit through 64 for {n} at multiplier {candidate}')
    return dict(n=n, factors=[p, q], scales_tested=split['scales_tested'],
                period_from_recovered_factors=period, rejecting_witnesses=witnesses, unit_powers=powers)


def main():
    for case in json.loads(FIXTURE.read_text()):
        measured = measure(int(case['n']))
        # The selection parameters and expected factors enter only after the split and period checks.
        expected = list(map(int, case['factors']))
        roots = [case['A']+i for i in case['indices']]
        assert expected == [x*x*case['t']+1 for x in roots] == measured['factors']
        common = gcd(*roots)
        assert measured['period_from_recovered_factors'] == case['period'] == (
            (roots[0]//common)*(roots[1]//common))**2
        assert measured['scales_tested'] == 1
        assert [(w['prime'], w['base']) for w in measured['rejecting_witnesses']] == [
            tuple(pair) for pair in case['rejecting_bases']]
        print(json.dumps(measured))


if __name__ == '__main__':
    main()
