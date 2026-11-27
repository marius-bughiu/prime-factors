"""Compare two public residue-band exclusions on three small balanced products."""

import argparse
import json
from math import isqrt, prod
from pathlib import Path

from experiments.jacobi_scale_gcd_screen import PRIMES, predecessor_powers, scan
from experiments.jacobi_square_scale_sieve import PERIOD, make_table


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-scale-prime-remainder.json'


def residue_in_band(lo, hi, residue, modulus, odd):
    first = lo + (residue - lo) % modulus
    if odd and first % 2 == 0:
        if modulus % 2 == 0:
            return False
        first += modulus
    return first <= hi


def exclusions(n, lo, hi, powers, odd):
    excluded = []
    incidental = []
    probes = 0
    for prime in PRIMES:
        power = powers.get(prime, 1)
        if prime * power**2 >= n:
            continue  # Every multiple already fails the height test.
        modulus = prime * power
        remainder = n % modulus
        if remainder == 0:
            incidental.append(prime)
        # Charge for both progressions even when the first one hits.
        hits = [residue_in_band(lo, hi, r, modulus, odd) for r in (1, remainder)]
        probes += 2
        if not any(hits):
            excluded.append(prime)
    return excluded, incidental, probes


def screened_counts(candidates, excluded, first_scale):
    roots = checks = 0
    for scale in candidates:
        for prime in excluded:
            checks += 1
            if scale % prime == 0:
                break
        else:
            roots += 1
            continue
        assert scale != first_scale
    return dict(excluded_primes=excluded, scale_modulos=checks, scale_roots=roots)


def measure(n, cap, offsets):
    if n % 2 != 1 or not 1 < cap < n <= 10_000:
        raise ValueError('expected an odd toy product up to 10,000 and a cap strictly below it')
    prepared = predecessor_powers(n)
    power_pairs = prepared['prime_powers']
    first_scale, decoded, totals = scan(n, cap, offsets, power_pairs)
    assert first_scale is not None  # The fixture compares searches that reach a split.
    candidates = []
    for block in range(0, first_scale, PERIOD):
        for offset in offsets:
            scale = block + offset
            if scale > first_scale:
                break
            divisor = prod(power for prime, power in power_pairs if scale % prime == 0)
            if scale * divisor**2 < n:
                candidates.append(scale)
    assert len(candidates) == totals['scale_roots'] and candidates[-1] == first_scale
    lo, hi = isqrt((n-1)//2) + 1, isqrt(n)
    trial_divisions = 0
    direct = None
    for possible in range(lo if lo % 2 else lo+1, hi+1, 2):
        trial_divisions += 1
        if n % possible == 0:
            direct = possible
            break
    measured = dict(band=[lo, hi], first_scale=first_scale, height_scale_roots=len(candidates),
                    predecessor_divmods=prepared['divmods'], direct_odd_trial_divisions=trial_divisions)
    for key, odd in [('full_band', False), ('odd_band', True)]:
        excluded, incidental, probes = exclusions(n, lo, hi, dict(power_pairs), odd)
        measured[key] = screened_counts(candidates, excluded, first_scale)
    # These preparatory remainders are identical in both lanes. A zero can itself reveal a factor.
    measured.update(setup_modulus_remainders=probes//2, setup_progression_tests=probes,
                    setup_incidental_prime_divisors=incidental)
    return measured, decoded, direct


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='verify operation counts against the fixture')
    args = parser.parse_args()
    fixture = json.loads(FIXTURE.read_text())
    offsets, _ = make_table()
    for case in fixture['products']:
        n = int(case['n'])
        measured, decoded, direct = measure(n, fixture['cap'], offsets)
        # Expected factors validate the previous first success and the independent direct baseline.
        p, q = map(int, case['factors'])
        assert p*q == n and 1 < p <= q <= 2*p and decoded == direct == p
        if args.check:
            assert case['observed'] == measured, (n, measured)
        print(json.dumps(dict(n=n, **measured)))


if __name__ == '__main__':
    main()
