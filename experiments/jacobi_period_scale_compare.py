"""Compare ascending predecessor-square scales and exact public period guesses on small semiprimes."""

import json
from math import gcd, isqrt
from pathlib import Path

from experiments.predecessor_square import factor_from_sum, search


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-period-scales.json'
FULL_SIZE = FIXTURE.with_name('predecessor-square.json')


def compare(n):
    """Both searches take only a balanced product of distinct primes at least seven."""
    scale = search(n, n)
    if scale['factor'] is None:
        raise ValueError(f'No successful scale through the public bound {n}')
    units = []
    first_nonunit = None
    for base in range(1, n):
        divisor = gcd(base, n)
        if divisor == 1:
            units.append(base)
        elif first_nonunit is None:
            first_nonunit = dict(base=base, factor=divisor)

    powers = 0
    for t in range(1, n+1):
        # Reject each incorrect guess at its first failing unit in ascending order.
        for base in units:
            powers += 1
            if pow(base, (n-1)*t, n) != 1:
                break
        else:
            root = isqrt(n//t)
            total = n+1 - t*root**2
            return dict(first_scale=scale['scales_tested'], scale_factor=scale['factor'],
                        first_period=t, period_sum=total, period_factor=factor_from_sum(n, total),
                        unit_membership_gcds=n-1, first_nonunit=first_nonunit, units=len(units),
                        unit_powers=powers)
    raise ValueError(f'No shared period through the public bound {n}')


def main():
    for case in json.loads(FIXTURE.read_text()):
        n = int(case['n'])
        measured = compare(n)
        for key in ('first_scale', 'first_period', 'unit_powers'):
            assert measured[key] == case[key], (n, key, measured[key])
        # The known factors enter only after the independent searches finish.
        p, q = map(int, case['factors'])
        assert p*q == n and 7 <= p < q <= 2*p
        assert measured['scale_factor'] == measured['period_factor'] == p
        assert measured['period_sum'] == p+q
        assert measured['first_nonunit'] == dict(base=p, factor=p)
        assert measured['units'] == (p-1)*(q-1)
        g = gcd(p-1, q-1)
        assert measured['first_period'] * g**2 == (p-1)*(q-1)
        print(json.dumps(dict(n=n, **measured)))

    # Replay the existing full-size scale budgets. Only a successful split
    # supplies the factors needed to read the theoretical minimum period.
    for case in json.loads(FULL_SIZE.read_text()):
        n = int(case['n'])
        split = search(n, case['max_scale'])
        assert split['scales_tested'] == case['scales_tested']
        p = split['factor']
        period_bits = None
        if p is not None:
            q = n//p
            assert n == p*q and [p, q] == list(map(int, case['factors']))
            g = gcd(p-1, q-1)
            period = ((p-1)//g)*((q-1)//g)
            period_bits = period.bit_length()
            if case['id'] == 'predecessor-square-2048':
                assert g == 6 and 6*isqrt(period//6)**2 == period and period_bits == 2043
        assert (p is not None) == (case['status'] == 'complete')
        print(json.dumps(dict(case=case['id'], scales_tested=split['scales_tested'],
                              split_found=p is not None, period_bits_from_split=period_bits)))


if __name__ == '__main__':
    main()
