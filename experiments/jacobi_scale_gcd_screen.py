"""Count integer operations in two first-scale searches on bounded balanced products."""

import json
from math import isqrt
from pathlib import Path

from experiments.jacobi_square_scale_sieve import PERIOD, make_table
from experiments.predecessor_square import factor_from_sum


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-scale-gcd-screen.json'
PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)


def predecessor_powers(n):
    """One divmod per trial, including the failed trial ending each prime's loop."""
    remaining = n - 1
    powers = []
    trials = 0
    extracted = 0
    for prime in PRIMES:
        if remaining == 1:
            break
        power = 1
        while True:
            quotient, remainder = divmod(remaining, prime)
            trials += 1
            if remainder:
                break
            remaining = quotient
            power *= prime
            extracted += 1
        if power > 1:
            powers.append([prime, power])
    return dict(prime_powers=powers, remaining_cofactor=remaining, divmods=trials,
                extracted_prime_factors=extracted)


def scan(n, cap, offsets, powers=None):
    """An optional list of (prime, full prime power) enables the added checks."""
    counts = dict(wheel_reads=0, candidates=0, support_modulos=0, support_products=0,
                  height_checks=0, height_rejections=0, scale_roots=0, scale_divisions=0,
                  root_modulos=0, root_rejections=0, sum_window_checks=0,
                  discriminant_roots=0)
    four_n, nine_n = 4*n, 9*n
    for block in range(0, cap, PERIOD):
        for offset in offsets:
            counts['wheel_reads'] += 1
            scale = block + offset
            if scale > cap:
                break
            counts['candidates'] += 1
            divisor = 1
            if powers is not None:
                for prime, power in powers:
                    counts['support_modulos'] += 1
                    if scale % prime == 0:
                        counts['support_products'] += 1
                        divisor *= power
            # All fixture caps are below n, so the d=1 height check is automatic.
            if divisor > 1:
                counts['height_checks'] += 1
                if scale * divisor**2 >= n:
                    counts['height_rejections'] += 1
                    continue
            counts['scale_roots'] += 1
            if scale == 1:
                root = isqrt(n) - 1
            else:
                counts['scale_divisions'] += 1
                root = isqrt(n // scale)
            if divisor > 1:
                counts['root_modulos'] += 1
                if root % divisor:
                    counts['root_rejections'] += 1
                    continue
            total = n + 1 - scale*root**2
            counts['sum_window_checks'] += 1
            square = total**2
            if square < four_n or 2*square > nine_n:
                continue
            # The shared window guarantees nonnegative discriminant. The decoder
            # takes exactly one square root here and checks the returned divisor.
            counts['discriminant_roots'] += 1
            factor = factor_from_sum(n, total)
            if factor is not None:
                return scale, factor, counts
    return None, None, counts


def compare(n, cap, offsets, prepared):
    if n <= 1 or not 0 <= cap < n:
        raise ValueError('these bounded controls require n > 1 and 0 <= cap < n')
    stop, factor, wheel = scan(n, cap, offsets)
    screened_stop, screened_factor, screened = scan(n, cap, offsets, prepared['prime_powers'])
    assert (stop, factor) == (screened_stop, screened_factor), (n, cap, stop, screened_stop)
    assert wheel['candidates'] == screened['candidates']
    assert screened['scale_roots'] + screened['height_rejections'] == screened['candidates']
    assert screened['sum_window_checks'] + screened['root_rejections'] == screened['scale_roots']
    return stop, factor, wheel, screened


def main():
    fixture = json.loads(FIXTURE.read_text())
    assert fixture['preparation_prime_limit'] == PRIMES[-1]
    offsets, divisions = make_table()
    assert fixture['shared_wheel'] == dict(period=PERIOD, residues=PERIOD,
        retained_offsets=len(offsets), construction_modulos=divisions)
    for case in fixture['products']:
        n = int(case['n'])
        prepared = predecessor_powers(n)
        assert prepared == case['preparation'], n
        for entry in case['runs']:
            cap = entry['cap']
            stop, factor, wheel, screened = compare(n, cap, offsets, prepared)
            assert stop == entry['first_scale'], (n, cap, stop)
            assert wheel == entry['wheel_only'], (n, cap, wheel)
            assert screened == entry['gcd_screen'], (n, cap, screened)
            # Expected factors enter only after both product-only scans finish.
            p, q = map(int, case['factors'])
            assert p*q == n and 1 < p < q <= 2*p
            assert factor == (None if stop is None else p)
            print(json.dumps(dict(n=str(n), cap=cap, first_scale=stop,
                                  preparation=prepared, wheel_only=wheel, gcd_screen=screened)))


if __name__ == '__main__':
    main()
