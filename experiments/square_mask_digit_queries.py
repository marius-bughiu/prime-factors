"""Check nonadaptive square-mask digit readings by exhaustive Jacobi summation.

The query menus, both recovered digits, and the trial-division interval use N
and the promise of distinct odd primes p < q < 2p. Reference factors check the
completed readout and the exact value of each query, including all zero bits.
"""

import json
from collections import Counter
from math import isqrt
from pathlib import Path

from experiments.jacobi_square_masks import complete_sum, mask_from_roots
from scripts.factor import primes_through


FIXTURE = Path(__file__).resolve().parents[1] / 'benchmarks/square-mask-digit-queries.json'


def digit_queries(n):
    """Run the same predetermined set of queries independently of earlier answers."""
    cutoff = isqrt(n) // 2
    radix = isqrt(cutoff) + 1
    bits = (radix - 1).bit_length()
    block = [(j, cutoff - 2 * radix * j) for j in range(radix)
             if cutoff - 2 * radix * j > 0]
    offset = [(i, cutoff + 1 - 2 * i) for i in range(radix)
              if cutoff + 1 - 2 * i > 0]
    digits = {'block': 0, 'offset': 0}
    rows = []
    work = Counter()
    for axis in digits:
        for bit in range(bits):
            weight = 1 << bit
            coords = ([x for j, x in block if axis != 'block' or j & weight]
                      + [y for i, y in offset if axis != 'offset' or i & weight])
            d = len(coords)
            roots = [x*x for x in coords]
            reading = complete_sum(n, mask_from_roots(roots))
            if d == 0 or reading not in (d*d, d*(d-1)):
                raise ArithmeticError(f'Unexpected square-mask reading for {n}, {axis}, bit {bit}')
            hit = reading < d*d
            if hit:
                digits[axis] += weight
            rows.append(dict(digit=axis, bit=bit, degree=d, distinct_baseline=d*d,
                             complete_sum=reading, recovered_bit=int(hit)))
            work.update(complete_sums=1, jacobi_evaluations=n, root_squares=d,
                        modular_root_multiplications=n*d, final_integer_multiplications=2*n)
    s = radix * digits['block'] + digits['offset']
    p = 2*cutoff + 1 - 2*s
    if not 1 < p < n or n % p:
        raise ArithmeticError(f'Digit reading at {n} decoded an invalid divisor')
    work['decoded_divisibility_checks'] = 1
    return dict(cutoff=cutoff, radix=radix, bits_per_digit=bits,
                block_digit=digits['block'], offset_digit=digits['offset'],
                decoded_offset=s, queries=rows, query_work=dict(work)), p


def odd_trial(n):
    """Stop at the first divisor in each direction inside sqrt(N/2) < p ≤ sqrt(N)."""
    low = isqrt(n // 2) + 1
    candidates = range(low if low % 2 else low + 1, isqrt(n) + 1, 2)

    def scan(values):
        for checks, value in enumerate(values, 1):
            if n % value == 0:
                return value, checks
        raise ArithmeticError(f'Public balanced interval contains no divisor at {n}')

    ascending, asc_checks = scan(candidates)
    descending, desc_checks = scan(reversed(candidates))
    if ascending != descending:
        raise ArithmeticError(f'Inconsistent trial divisors at {n}')
    return ascending, dict(odd_interval_candidates=len(candidates),
                           ascending_divisibility_checks=asc_checks,
                           descending_divisibility_checks=desc_checks)


def check_product(n, reference_p, reference_q):
    reading, decoded = digit_queries(n)
    from_trial, trial_work = odd_trial(n)
    if (decoded, n//decoded) != (reference_p, reference_q) or from_trial != decoded:
        raise ArithmeticError(f'Factor verification failed at {n}')
    expected_s = (2*reading['cutoff'] + 1 - reference_p) // 2
    block, offset = divmod(expected_s, reading['radix'])
    for row in reading['queries']:
        target = block if row['digit'] == 'block' else offset
        expected_bit = (target >> row['bit']) & 1
        d = row['degree']
        if row['complete_sum'] != d*(d-expected_bit):
            raise ArithmeticError(f'Incorrect exact query or bit at {n}: {row}')
    return reading, trial_work


def study():
    cohorts = []
    example = None
    primes = [p for p in primes_through(63) if p % 2]
    for width in range(3, 7):
        totals = Counter()
        for q in primes:
            if q.bit_length() != width:
                continue
            for p in primes:
                if not p < q < 2*p:
                    continue
                n = p*q
                reading, trial = check_product(n, p, q)
                totals['products'] += 1
                totals.update(reading['query_work'])
                totals.update(trial)
                if n == 2183:
                    # Swap the two read-out digits while preserving every measured sum.
                    wrong_s = reading['radix']*reading['offset_digit'] + reading['block_digit']
                    wrong = 2*reading['cutoff'] + 1 - 2*wrong_s
                    if wrong == p or n % wrong == 0:
                        raise ArithmeticError('The swapped-digit control unexpectedly passed')
                    example = dict(product=str(n), reference_prime_factors=[str(p), str(q)],
                                   **reading, trial_division=trial,
                                   swapped_digits=dict(decoded_offset=wrong_s, candidate=str(wrong),
                                                       remainder=n % wrong))
        cohorts.append(dict(larger_prime_bits=width, **totals))
    if example is None:
        raise ArithmeticError('Missing 2183 control')
    return dict(population='All distinct odd primes p < q < 2p with q of 3 through 6 bits.',
                cohorts=cohorts, example=example)


if __name__ == '__main__':
    result = study()
    if result != json.loads(FIXTURE.read_text()):
        raise SystemExit('Square-mask digit-query census differs from the reviewed fixture')
    count = sum(row['products'] for row in result['cohorts'])
    print(f'Checked exact digit queries and both odd trial scans on {count} balanced products.')
