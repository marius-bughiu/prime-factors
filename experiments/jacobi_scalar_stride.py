"""Measure single-phase scalar periods from public Jacobi sums on small semiprimes."""

from collections import defaultdict
import json
from math import gcd, isqrt
from pathlib import Path

from experiments.jacobi_four_width import read_factors
from experiments.jacobi_moment_periods import first_repeating_shift
from experiments.projective_word_moments import jacobi


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-scalar-stride.json'


def scalar_period(n, signs, stride):
    """Group equal powered residues, then certify a full cycle of the scalar sequence.

    At an odd squarefree semiprime, each residue's positive even powers are
    periodic modulo both primes. The weighted state at degree 2s therefore
    returns within lcm((p-1)/2, (q-1)/2) < n steps, even for nonunit bases.
    A complete state cycle bounds the period of the scalar sum. Different
    states may have equal sums, so check all shifts of the recorded cycle.
    """
    weights = defaultdict(int)
    for residue, sign in enumerate(signs):
        base = pow(residue, 2*stride, n)
        weights[base] += sign

    bases = []
    first = []
    for base, weight in weights.items():
        term = base*weight % n
        if term:
            bases.append(base)
            first.append(term)

    state = first
    cycle = []
    for _ in range(n):
        cycle.append(sum(state) % n)
        state = [term*base % n for term, base in zip(state, bases)]
        if state == first:
            break
    else:
        raise ValueError('state failed to return within the semiprime bound')

    period = first_repeating_shift(cycle+cycle, len(cycle))
    work = dict(residue_powers=n, weight_additions=n, powered_residue_buckets=len(weights),
                initial_weight_products=len(weights), active_weighted_buckets=len(bases),
                scalar_moments=len(cycle), sum_additions=len(bases)*len(cycle),
                term_updates=len(bases)*len(cycle),
                state_comparison_entry_bound=len(bases)*len(cycle), tested_scalar_shifts=period,
                scalar_comparison_entry_bound=period*len(cycle))
    return dict(stride=stride, scalar_period=period, state_period=len(cycle), work=work)


def recover(n, reduced_product):
    common = isqrt(n//(4*reduced_product))
    total = n+1 - 4*common*common*reduced_product
    return dict(candidate_sum=total, factors=read_factors(n, total))


def measure(n):
    """Only the public product is passed to the measurement and the baselines."""
    if n < 9 or n % 2 == 0:
        raise ValueError('expected a product of two distinct odd primes')
    signs = [jacobi(t*t-4, n) for t in range(n)]
    half = (n-1)//2
    two_part = half & -half
    ordinary = scalar_period(n, signs, 1)
    half_stride = scalar_period(n, signs, half)
    odd_stride = scalar_period(n, signs, half//two_part)

    raw_period = half_stride['scalar_period']
    odd_period = odd_stride['scalar_period']
    half_stride['readout'] = recover(n, raw_period)
    multiplier = gcd(two_part, odd_period)
    odd_stride['dyadic_multiplier'] = multiplier
    odd_stride['readout'] = recover(n, multiplier*odd_period)

    # The first vanishing Jacobi symbol with a proper gcd already splits N.
    zero_gcds = 0
    for t, sign in enumerate(signs):
        if sign == 0:
            zero_gcds += 1
            divisor = gcd(t*t-4, n)
            if 1 < divisor < n:
                break
    else:
        raise ValueError('no splitting zero found')

    divisor_tests = 0
    for candidate in range(3, isqrt(n)+1, 2):
        divisor_tests += 1
        if n % candidate == 0:
            break
    else:
        raise ValueError('trial division found no factor')

    center = isqrt(n)
    center += int(center*center < n)
    start = center
    while True:
        gap_squared = center*center-n
        gap = isqrt(gap_squared)
        if gap*gap == gap_squared:
            break
        center += 1

    return dict(shared_jacobi_signs=n, ordinary=ordinary,
                half_predecessor=half_stride, odd_predecessor=odd_stride,
                first_splitting_zero=dict(signs_through_hit=t+1, zero_gcds=zero_gcds, factor=divisor),
                trial_division=dict(odd_divisor_tests=divisor_tests, factor=candidate),
                fermat=dict(square_tests=center-start+1, factors=[center-gap, center+gap]))


def main():
    for case in json.loads(FIXTURE.read_text()):
        n = int(case['n'])
        result = measure(n)
        for key in ('ordinary', 'half_predecessor', 'odd_predecessor'):
            assert result[key]['scalar_period'] == case[key], (n, key, result[key])
        assert result['odd_predecessor']['dyadic_multiplier'] == case['dyadic_multiplier']
        p, q = map(int, case['factors'])
        assert p*q == n
        assert result['odd_predecessor']['readout']['factors'] == [p, q]
        raw_factors = result['half_predecessor']['readout']['factors']
        assert raw_factors == ([p, q] if case['raw_readout_splits'] else None)
        assert result['first_splitting_zero']['factor'] in (p, q)
        assert result['trial_division']['factor'] == p
        assert result['fermat']['factors'] == [p, q]
        print(json.dumps(dict(n=n, **result)))


if __name__ == '__main__':
    main()
