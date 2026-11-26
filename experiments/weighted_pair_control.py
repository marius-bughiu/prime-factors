"""Construct a planted full-size example for the first two weighted square tests.

Search nearby lattice points around the fixed ratio (137-48 sqrt(2))/49.
Both primes are 1 modulo 2^496 so the existing partial-order primality
certificate can often exploit other small factors of their predecessors.
The independent factor search receives only the resulting product. By
default replay the selected vector. --discover repeats the bounded search.
"""

import argparse
import json
import sys
from math import gcd, isqrt, prod
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.weighted_square_pairs import first_label, search
from scripts.factor import prime_witness, primes_through, render_certificate, verify_file


REPO = Path(__file__).resolve().parents[1]
RECORD = REPO / 'research/weighted-pair-control.json'
PROOF = REPO / 'benchmarks/controls/WeightedPairControl.lean'
MODULUS = 1 << 496
ROW_LIMIT = 5000
SELECTED = (24128, 4174)


def lattice_basis():
    scale = 1 << 2200
    numerator = (137*scale - 48*isqrt(2*scale*scale)) // 49
    a, b = numerator, scale
    previous, current = (1, 0), (0, 1)  # denominator, numerator
    while b:
        quotient, remainder = divmod(a, b)
        following = (previous[0] + quotient*current[0],
                     previous[1] + quotient*current[1])
        if following[0].bit_length() >= 513:
            return following, current
        previous, current = current, following
        a, b = b, remainder
    raise ArithmeticError('continued fraction terminated too early')


def record_for(p, q, i, j):
    n = p*q
    # Certify q < ((137-48√2)/49)p < q+2 without rounding either radical.
    gap = 137*p-49*q
    if not (0 < gap-98 and (gap-98)**2 < 2*(48*p)**2 < gap*gap):
        return None
    a, sa = first_label(n, 1)
    b, sb = first_label(n, 2)
    d, e = a*a-4*n, b*b-8*n
    if not (p.bit_length() == q.bit_length() == 1024 and n.bit_length() == 2048 and p < q and
            3*a == 17*p-7*q and 8*b == 17*p+7*q and (sa, sb) == (12, 2) and
            9*d == 64*e and isqrt(d)**2 != d and isqrt(e)**2 != e):
        return None
    if prime_witness(p) is None or prime_witness(q) is None:
        return None
    hit = search(n)
    if hit['factor'] != q:
        raise ArithmeticError('independent cross-row computation missed the planted case')
    return dict(id='first-weighted-pair-planted-2048', n=str(n),
                expected_factors=[str(p), str(q)], lattice_indices=[i, j],
                labels=hit['labels'], excesses=hit['excesses'], square_root=hit['root'])


def construct():
    (u, v), (w, z) = lattice_basis()
    i, j = SELECTED
    record = record_for(1+MODULUS*(i*u+j*w), 1+MODULUS*(i*v+j*z), i, j)
    if record is None:
        raise ArithmeticError('selected vector no longer gives the documented prime pair')
    return record


def discover():
    (u, v), (w, z) = lattice_basis()
    ceiling = 1 << 1024
    lower, upper = 5*ceiling//8, 11*ceiling//16
    primorial = prod(primes_through(1300))
    tested = 0
    survivors = 0
    # Solve (1 + M*(i*v+j*z)) = 5*(1 + M*(i*u+j*w)) modulo 9.
    inverse = pow(MODULUS*(v-5*u), -1, 9)
    for j in range(ROW_LIMIT):
        start = (lower-1-MODULUS*j*w+MODULUS*u-1) // (MODULUS*u)
        stop = (upper-1-MODULUS*j*w+MODULUS*u-1) // (MODULUS*u)
        residue = (4-MODULUS*j*(z-5*w))*inverse % 9
        for i in range(start+(residue-start)%9, stop, 9):
            p = 1+MODULUS*(i*u+j*w)
            q = 1+MODULUS*(i*v+j*z)
            tested += 1
            if gcd(p, primorial) != 1 or gcd(q, primorial) != 1:
                continue
            survivors += 1
            if pow(2, p-1, p) != 1 or pow(2, q-1, q) != 1:
                continue
            record = record_for(p, q, i, j)
            if record is not None:
                return record, tested, survivors
    raise RuntimeError(f'no certified control in the first {ROW_LIMIT} lattice rows')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='compare against the published record')
    parser.add_argument('--verify', action='store_true', help='regenerate and kernel-check the proof')
    parser.add_argument('--discover', action='store_true', help='repeat the original bounded selection')
    args = parser.parse_args()
    record = construct()
    if args.discover:
        found, tested, survivors = discover()
        if found != record:
            raise ValueError('the first certified discovery differs from the selected vector')
        print(f'Construction tested {tested} candidate pairs, {survivors} passed the small sieve.',
              file=sys.stderr)
    if args.check and json.loads(RECORD.read_text()) != record:
        raise ValueError('the reconstructed control differs from the published record')
    if args.verify:
        proof_text = render_certificate(int(record['n']), list(map(int, record['expected_factors'])))
        with TemporaryDirectory() as directory:
            path = Path(directory) / 'WeightedPairControl.lean'
            path.write_text(proof_text)
            verify_file(path)
        if args.check and PROOF.read_text() != proof_text:
            raise ValueError('the regenerated Lean proof differs from the published proof')
    if not args.check:
        print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
