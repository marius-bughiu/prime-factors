"""Reconstruct the two deliberately perturbed, Pocklington-friendly prime pairs.

The factor search accepts only the product and tolerance. This generator uses
separate fixed seeds and records the first successful index after a prime sieve.
"""

import argparse
from hashlib import sha256, sha512
from math import gcd

from .smooth_sum_control import planted_sum
from scripts.factor import prime_witness, primes_through


KNOWN_INDICES = {1: 103627, 2: 2525}


def progression(version):
    if version == 1:
        digest = sha256(b'near-two-three-sum-v1').digest()
        multiplier = (int.from_bytes(digest, 'big') % 2**80) | 2**79 | 1
    elif version == 2:
        digest = sha512(b'near-two-three-sum-v2').digest()
        multiplier = (int.from_bytes(digest, 'big') % 2**319) | 2**318 | 1
        while multiplier % 3 != 1:
            multiplier -= 2
    else:
        raise ValueError('version must be 1 or 2')
    total = planted_sum() + 2 + 2**80 * multiplier
    power_three = 1
    while power_three < 2**433:
        power_three *= 3
    power_two = 2**513
    step = power_two * power_three
    # p=1 mod 3^274, q=1 mod 2^513 and p=1 mod 2^80. Hence both
    # (p-1) and (q-1) have publicly factored parts greater than sqrt(p), sqrt(q).
    start = (total-1 + power_two*((2-total)*pow(power_two, -1, power_three) % power_three)) % step
    lower = max(3*2**1022, total-(2**1024-1))
    first = start + step*((lower-start+step-1)//step)
    return total, first, step


def construct(version, *, replay=False):
    total, first, step = progression(version)
    limit = KNOWN_INDICES[version] + 1
    if replay:
        possible = bytearray([1])*limit
        for ell in primes_through(10000):
            if step % ell == 0:
                if gcd(first*(total-first), ell) != 1:
                    raise ArithmeticError('construction progression has a fixed small factor')
                continue
            inverse = pow(step, -1, ell)
            for value in (-first, total-first):
                residue = value*inverse % ell
                possible[residue::ell] = bytes(max(0, (limit-1-residue)//ell + 1))
        indices = (i for i in range(limit) if possible[i])
    else:
        indices = [limit-1]
    for index in indices:
        p = first + index*step
        q = total-p
        if not (p < q and p.bit_length() == q.bit_length() == 1024
                and (p*q).bit_length() == 2048 and q-p >= 2**1020):
            raise ArithmeticError('candidate fell outside construction band')
        if prime_witness(p) and prime_witness(q):
            if index != limit-1:
                raise ArithmeticError('an earlier certified pair was found')
            return p, q
    raise ArithmeticError('could not reconstruct certified pair')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('version', type=int, choices=(1, 2))
    parser.add_argument('--replay', action='store_true')
    args = parser.parse_args()
    p, q = construct(args.version, replay=args.replay)
    print(p*q)
