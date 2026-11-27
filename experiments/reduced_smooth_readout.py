"""One gcd after sweeping prime powers on a product-derived reduced base."""

import argparse
import json
from math import gcd

from scripts.factor import primes_through


def blocks(bound, factor_bits):
    """Largest power of each listed prime below the public factor cap."""
    cap = (1 << factor_bits) - 1
    for prime in primes_through(bound):
        power = prime
        if power > cap:
            break
        while power <= cap // prime:
            power *= prime
        yield prime, power


def search(n, bound, factor_bits, base_limit):
    """Search from the product only. An exhausted accepted run certifies a divisibility exclusion."""
    if n < 3 or bound < 2 or factor_bits < 1 or base_limit < 2:
        raise ValueError('expected a modulus at least 3 and positive search bounds')
    work = dict(bound=bound, factor_bits=factor_bits, base_limit=base_limit,
                bases=0, base_gcds=0, initial_powers=0, accepted_base=None,
                blocks=0, last_prime=None, exponent_bits=0, readout_gcds=0,
                source='base budget exhausted')
    for base in range(2, min(base_limit, n-1) + 1):
        work['bases'] += 1
        divisor = gcd(base, n)
        work['base_gcds'] += 1
        if divisor > 1:
            work['source'] = 'base gcd'
            return divisor, work
        residue = pow(base, n-1, n)
        work['initial_powers'] += 1
        if residue != 1:
            work['accepted_base'] = base
            break
    else:
        return None, work

    previous = residue
    for prime, power in blocks(bound, factor_bits):
        previous, residue = residue, pow(residue, power, n)
        work['blocks'] += 1
        work['last_prime'] = prime
        work['exponent_bits'] += power.bit_length()
        if residue == 1:
            break
    stopped = residue == 1
    choice = previous if stopped else residue
    divisor = gcd(choice-1, n)
    work['readout_gcds'] = 1
    if 1 < divisor < n:
        work['source'] = 'before identity' if stopped else 'last residue'
        return divisor, work
    if stopped:
        # Composite inputs with more than two distinct factors or repeated
        # prime factors can reach the identity without a proper predecessor gcd.
        work['source'] = 'identity without split'
    else:
        work['source'] = 'smoothness sweep exhausted'
    return None, work


def ordinary_sweep(n, base, bound, factor_bits):
    """Classical p−1 comparison at the same base, testing each prime-power checkpoint."""
    residue = base % n
    count = gcds = bits = refinement_powers = refinement_bits = 0
    for prime, power in blocks(bound, factor_bits):
        previous = residue
        residue = pow(residue, power, n)
        count += 1
        bits += power.bit_length()
        divisor = gcd(residue-1, n)
        gcds += 1
        if divisor == n:
            # When a checkpoint saturates, also test the smaller powers of this prime.
            exponent = 1
            while exponent < power:
                previous = pow(previous, prime, n)
                exponent *= prime
                refinement_powers += 1
                refinement_bits += prime.bit_length()
                divisor = gcd(previous-1, n)
                gcds += 1
                if divisor != 1:
                    break
            return (divisor if 1 < divisor < n else None), dict(
                blocks=count, gcds=gcds, exponent_bits=bits, saturated=True,
                refinement_powers=refinement_powers, refinement_exponent_bits=refinement_bits)
        if divisor != 1:
            return divisor, dict(blocks=count, gcds=gcds, exponent_bits=bits, saturated=False,
                                 refinement_powers=0, refinement_exponent_bits=0)
    return None, dict(blocks=count, gcds=gcds, exponent_bits=bits, saturated=False,
                      refinement_powers=0, refinement_exponent_bits=0)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--bound', type=int, default=13)
    parser.add_argument('--factor-bits', type=int,
                        help='factor bit cap; defaults to the balanced-factor width')
    parser.add_argument('--base-limit', type=int, help='defaults to the squared product bit length')
    args = parser.parse_args()
    bits = args.factor_bits if args.factor_bits is not None else (args.n.bit_length()+1)//2
    bases = args.base_limit if args.base_limit is not None else args.n.bit_length()**2
    divisor, work = search(args.n, args.bound, bits, bases)
    print(json.dumps(dict(n=str(args.n), divisor=str(divisor) if divisor else None, work=work), indent=2))
