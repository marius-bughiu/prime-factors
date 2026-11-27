"""Compare complete even Jacobi moments with unit-power tests at stride (N−1)/2."""

import json
from math import gcd, lcm
from pathlib import Path

from experiments.jacobi_four_width import even_moments
from experiments.jacobi_moment_periods import first_repeating_shift


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-stride-period-tests.json'


def measure(n):
    """Use only the product of two distinct primes at least seven as input.

    The ordinary even sequence has a period below N by Fermat at both primes.
    Comparing blocks of N values therefore checks every phase of that sequence.
    Offsets start at zero, where the complete moment has degree two.
    """
    moments = even_moments(n, 2*n)
    full_period = first_repeating_shift(moments, n)
    cycle = moments[:full_period]
    stride = (n-1)//2
    orbit_count = gcd(stride, full_period)
    orbit_length = full_period//orbit_count
    offset_periods = []
    for offset in range(orbit_count):
        orbit = [cycle[(offset + k*stride) % full_period] for k in range(orbit_length)]
        offset_periods.append(first_repeating_shift(orbit + orbit, orbit_length))
    shared_period = lcm(*offset_periods)
    assert shared_period == orbit_length

    units = []
    first_factor = None
    for base in range(1, n):
        divisor = gcd(base, n)
        if divisor == 1:
            units.append(base)
        elif first_factor is None:
            first_factor = divisor

    shifts = {}
    early_passes = dict.fromkeys(units, 0)
    first_pass = {}
    for t in range(1, 2*shared_period + 1):
        matches = [j for j in range(full_period)
                   if cycle[j] == cycle[(j + stride*t) % full_period]]
        passing_bases = [base for base in units if pow(base, (n-1)*t, n) == 1]
        for base in passing_bases:
            first_pass.setdefault(base, t)
            if t < shared_period:
                early_passes[base] |= 1 << t
        passing_units = len(passing_bases)
        assert (len(matches) == full_period) == (t % shared_period == 0)
        assert passing_units * shared_period == len(units) * gcd(t, shared_period)
        shifts[t] = dict(matching_starts=len(matches), first_match=next(iter(matches), None),
                         passing_units=passing_units)

    # Every unit passes at the shared period, so its test repeats modulo that
    # period. An ordered pair is faithful exactly when its early passes are disjoint.
    good_pairs = 0
    witness = None
    for x in units:
        for y in units:
            if early_passes[x] & early_passes[y] == 0:
                good_pairs += 1
                if witness is None and first_pass[x] < first_pass[y] < shared_period:
                    witness = dict(bases=[x, y], first_passes=[first_pass[x], first_pass[y]])
    panels = dict(good_pairs=good_pairs, ordered_pairs=len(units)**2, witness=witness)
    assert 2*good_pairs > panels['ordered_pairs']

    work = dict(jacobi_signs=n, even_moments=len(moments), weighted_term_updates=n*len(moments),
                unit_membership_gcds=n-1, first_factor_from_membership=first_factor,
                proposed_shifts=len(shifts), unit_powers=len(shifts)*len(units))
    return dict(stride=stride, full_period=full_period, offset_periods=offset_periods,
                shared_period=shared_period, units=len(units), shifts=shifts, panels=panels, work=work)


def main():
    for case in json.loads(FIXTURE.read_text()):
        n = int(case['n'])
        result = measure(n)
        for key in ('full_period', 'offset_periods', 'shared_period', 'units', 'panels'):
            assert result[key] == case[key], (n, key, result[key])
        measured = result.pop('shifts')
        probes = {t: measured[int(t)] for t in case['probes']}
        assert probes == case['probes'], (n, probes)
        p, q = map(int, case['factors'])
        assert p*q == n and result['units'] == (p-1)*(q-1)
        assert result['work']['first_factor_from_membership'] == p
        print(json.dumps(dict(n=n, **result, probes=probes)))


if __name__ == '__main__':
    main()
