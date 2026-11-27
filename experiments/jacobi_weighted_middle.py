"""Check a single-pass weighted Jacobi sum on bounded, synthetic balanced semiprimes."""

import json
from math import comb, gcd, isqrt
from pathlib import Path

from experiments.gap_coverage import fermat, square_factor
from experiments.jacobi_middle_degree import moment
from experiments.projective_word_moments import jacobi


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/jacobi-weighted-middle.json'


def weighted_sum(n, j):
    """Stream one sign and at most one modular power per residue."""
    degree = 2*j
    constant = 4*j + 2
    value = powers = gcd_checks = 0
    incidental = None
    for x in range(n):
        square = x*x
        sign = jacobi(square-4, n)
        if sign == 0:
            # A zero sign detects a shared divisor for free. Identifying the
            # divisor still costs a gcd, and x=±2 can give the whole modulus.
            if incidental is None:
                gcd_checks += 1
                divisor = gcd(square-4, n)
                if 1 < divisor < n:
                    incidental = dict(residue=x, divisor=divisor, signs_read=x+1,
                                      powers_read=powers, explicit_gcds=gcd_checks)
            continue
        if x == 0:
            continue
        powers += 1
        weight = (j+1)*square - constant
        value = (value + sign*pow(x, degree, n)*weight) % n
    return dict(residue=value, divisor=gcd(value, n), signs=n, modular_powers=powers,
                final_gcds=1, first_incidental=incidental)


def trial_control(n):
    for checks, d in enumerate(range(3, isqrt(n)+1, 2), start=1):
        if n % d == 0:
            return dict(divisor=d, odd_trial_divisions=checks)
    raise ValueError('no proper divisor on the odd-trial control')


def measure(n):
    if n < 15 or n > 8191 or n % 2 == 0:
        raise ValueError('controls use odd products between 15 and 8191')
    j = isqrt(n)//2
    direct = weighted_sum(n, j)

    # Independent reference computes both complete moments separately with the
    # existing routine. It sets up its own common Jacobi table and uses every row.
    signs = [jacobi(x*x-4, n) for x in range(n)]
    low = moment(n, 2*j, signs)
    high = moment(n, 2*j+2, signs)
    combined = ((j+1)*high - (4*j+2)*low) % n
    assert combined == direct['residue']
    reference = dict(lower=low, upper=high, residue=combined, signs=n, modular_powers=2*n,
                     powers_if_zero_terms_skipped=2*direct['modular_powers'])

    first_midpoint = isqrt(n-1)+1
    first_difference = first_midpoint**2-n
    first_fermat_factor = square_factor(n, first_midpoint)
    fermat_run = fermat(n, n//2)
    assert fermat_run.factor and (first_fermat_factor > 1) == (fermat_run.squares == 1)
    fermat_data = dict(first_midpoint=first_midpoint, first_difference=first_difference,
                       first_square_hit=first_fermat_factor > 1, square_tests=fermat_run.squares,
                       divisor=fermat_run.factor)
    # For the combined route, one Fermat midpoint covers the narrow gaps. We
    # measured the unshortened weighted sum above even on these fallback cases.
    if first_fermat_factor > 1:
        route = 'first_fermat_square'
        pair = (first_fermat_factor, n//first_fermat_factor)
    elif 1 < direct['divisor'] < n:
        route = 'weighted_sum'
        pair = tuple(sorted((direct['divisor'], n//direct['divisor'])))
    else:
        raise AssertionError(f'neither the first Fermat square nor the weighted sum splits {n}')
    coefficient = comb(2*j, j)
    return dict(j=j, weighted=direct, two_moments=reference, trial=trial_control(n), fermat=fermat_data,
                central=dict(divisor=gcd(n, coefficient), coefficient_bits=coefficient.bit_length()),
                route=route, recovered=[str(x) for x in pair])


def main():
    for case in json.loads(FIXTURE.read_text()):
        n = int(case['n'])
        result = measure(n)
        # The supplied primes only validate the independent measurements.
        p, q = map(int, case['factors'])
        assert 7 <= p < q < 2*p and p*q == n
        assert result['recovered'] == case['factors']
        if q-p >= 6:
            assert result['weighted']['divisor'] == q
        else:
            assert result['fermat']['first_square_hit']
        assert result == case['observed'], (n, result)
        print(json.dumps(dict(n=n, **result)))


if __name__ == '__main__':
    main()
