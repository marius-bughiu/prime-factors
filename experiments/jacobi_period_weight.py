"""Compare the paired, weighted, and all-unit period tests on bounded public inputs."""

import json
from math import gcd, lcm
from pathlib import Path

from experiments.jacobi_four_width import even_moments
from experiments.projective_word_moments import jacobi


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-period-weight.json'


def measure(n, cap, second_probe=None):
    if not (3 <= n <= 1023 and n % 2 == 1 and 0 <= cap <= 128):
        raise ValueError('expected a bounded odd modulus and a shift ceiling at most 128')
    shifts = range(cap+1)
    # Obtain every adjacent pair from one sequence. This helper performs exactly
    # n sign evaluations, n modular squarings and n updates for each moment.
    moments = even_moments(n, cap+2)
    pairs = [d for d in shifts if moments[d] == 2 and moments[d+1] == 6]
    first = [d for d in shifts if moments[d] == 2 and d not in pairs]
    second = [d for d in shifts if moments[d+1] == 6 and d not in pairs]

    # The weighted test only needs x^(2*(d+1)) times (x^2-3). Reuse the
    # signs across shifts, but evaluate each surviving modular power and each gcd.
    terms = []
    for x in range(n):
        square = x*x % n
        sign = jacobi(square-4, n)
        weight = sign*(square-3) % n
        if weight and x:
            terms.append((x, weight))
    divisors = []
    for d in shifts:
        value = sum(weight*pow(x, 2*(d+1), n) for x, weight in terms) % n
        if value != (moments[d+1]-3*moments[d]) % n:
            raise AssertionError(f'weighted and paired implementations disagree at {d}')
        divisors.append(gcd(value, n))
    weighted = [d for d in shifts if divisors[d] == n]

    # A direct all-unit test is an independent deterministic period baseline.
    # Enumerate the units once, and stop at the first rejecting power for each shift.
    units = [x for x in range(1, n) if gcd(x, n) == 1]
    powers = 0
    periods = []
    for d in shifts:
        for x in units:
            powers += 1
            if pow(x, 2*d, n) != 1:
                break
        else:
            periods.append(d)
    result = dict(
        paired=pairs, only_first=first, only_second=second, weighted=weighted,
        unit_periods=periods,
        pair_work=dict(signs=n, modular_squarings=n, modular_term_updates=n*(cap+2)),
        weight_work=dict(signs=n, modular_squarings=n, modular_powers=(cap+1)*len(terms),
                         powers_per_shift=len(terms), final_gcds=cap+1),
        unit_work=dict(gcds=n-1, modular_powers=powers),
    )
    if second_probe is not None:
        if not 0 <= second_probe < cap:
            raise ValueError('the second probe needs three consecutive entries in the measured table')
        d = second_probe
        result['second_probe'] = dict(shift=d, first_weight=(moments[d+1]-3*moments[d]) % n,
                                      second_weight=(3*moments[d+2]-10*moments[d+1]) % n)
    return result, divisors


def main():
    for case in json.loads(FIXTURE.read_text()):
        n, cap = int(case['n']), case['shift_ceiling']
        result, divisors = measure(n, cap, case.get('second_probe_shift'))
        # Supplied factors only check the independently observed tests.
        p, q = map(int, case['factors'])
        assert 7 <= p < q and p*q == n
        period = lcm((p-1)//2, (q-1)//2)
        assert result['paired'] == result['unit_periods'] == list(range(0, cap+1, period))
        for d, divisor in enumerate(divisors):
            for prime in (p, q):
                local_zero = d % ((prime-1)//2) == 0 or (prime == 13 and d % 6 == 4)
                assert (divisor % prime == 0) == local_zero
        assert result == case['observed'], (n, result)
        print(json.dumps(dict(n=n, **result)))


if __name__ == '__main__':
    main()
