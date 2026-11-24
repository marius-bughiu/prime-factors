"""Recompute the combined CRT and continued-fraction exclusion on the crossed input.

Run from the repository root with python3 -m experiments.verify_crt_comparison.
The full product and remainder trees use the optional gmpy2 package.
"""

import json
from math import isqrt
from pathlib import Path

from gmpy2 import is_square, mpz, primorial

from .crt_square_norms import _local_roots, _nearby, _split_roots
from .pell_pairs import convergents
from .pell_relations import _private_parts


def fixed_input():
    path = Path(__file__).resolve().parents[1] / 'benchmarks' / 'crt-square-norms.json'
    return next(int(case['n']) for case in json.loads(path.read_text())
                if case['id'] == 'crt-square-crossed-2048')


def compare(n):
    roots, divisor = _local_roots(n, 32, {'primes_tested': 0})
    if divisor is not None:
        raise ValueError('the input has a factor among the screened primes')
    d, lefts, rights = _split_roots(roots)
    bound = isqrt(n) >> 26
    minimum, _, total, hits = _nearby(n, d, lefts, rights, bound, 512)
    if len(hits) != total:
        raise ValueError('the cap excludes CRT hits from this comparison')
    norms = []
    for t in hits:
        quotient, remainder = divmod(t*t - n, d*d)
        if remainder or abs(quotient) > bound:
            raise ArithmeticError('invalid CRT window representative')
        norms.append(mpz(abs(quotient)))

    steps = len(lefts) + len(rights)
    cf_minimum = None
    cf_hits = 0
    for _, absolute, sign, numerator, _ in convergents(n, 1, steps):
        if (numerator*numerator - sign*absolute) % n:
            raise ArithmeticError('invalid continued-fraction relation')
        norms.append(mpz(absolute))
        cf_minimum = absolute if cf_minimum is None else min(cf_minimum, absolute)
        cf_hits += absolute <= bound

    smooth_limit = 2**24
    private = _private_parts(norms, primorial(smooth_limit))
    nonsquares = [part for part in private if not is_square(part)]
    return dict(crt_minimum_bits=minimum.bit_length(), crt_hits=total,
                continued_fraction_steps=steps, continued_fraction_minimum_bits=cf_minimum.bit_length(),
                continued_fraction_hits=cf_hits, combined_rows=len(norms),
                smooth_limit=smooth_limit, nonsquare_private_parts=len(nonsquares),
                minimum_private_bits=min((x.bit_length() for x in nonsquares), default=None))


if __name__ == '__main__':
    print(json.dumps(compare(fixed_input()), indent=2))
