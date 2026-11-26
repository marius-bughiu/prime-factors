"""Rebuild two deliberately structured 2048-bit carry controls.

D=2^704, M is either 3^325 or 5^224. Choose a short signed remainder
v = uD (mod M). For t near a public starting size, P=1+t(uD-v) is
1 mod M and has the signed radix expansion (tu)D+(1-tv). The known
prime power M is larger than sqrt(P), facilitating a primality certificate.

The two pairs of Euclidean vector indices below were selected, not sampled.
The pilot considered the first 32 intermediate quotients at each division,
kept coefficients with 215..288 bits, then ranked the prospective pairs by
decreasing primitive weighted-trace distance at the initial odd candidates.
We retained certified examples with the requested carries. For the second
case we required both one-carry-only searches to fail and, when possible,
kept the leading coefficient odd. This script replays the selected four
progressions. The factor-search experiment sees only the resulting product.
"""

import argparse
import json
from math import gcd, isqrt, prod
from pathlib import Path
from tempfile import TemporaryDirectory

from .radix_carries import nearest
from scripts.factor import prime_witness, primes_through, render_certificate, verify_file


EXPONENT = 704
D = 1 << EXPONENT
LIMIT = 12_000
SMALL_PRIMES = prod(primes_through(1200))
RECORD = Path(__file__).resolve().parents[1] / 'research/radix-carry-controls.json'


def vectors(modulus):
    """Yield (u,v) with u positive and uD-v divisible by modulus."""
    previous, current = (0, modulus), (1, D % modulus)
    while current[1]:
        quotient = previous[1] // current[1]
        for partial in range(1, min(32, quotient) + 1):
            u = previous[0] - partial*current[0]
            v = previous[1] - partial*current[1]
            if u < 0:
                u, v = -u, -v
            if 215 <= u.bit_length() <= 288:
                yield u, v
        previous, current = current, (previous[0] - quotient*current[0],
                                      previous[1] - quotient*current[1])


def first_prime(modulus, start, index, prefer_odd):
    u, v = list(vectors(modulus))[index]
    step = u*D - v
    if step <= 0 or step % modulus:
        raise ArithmeticError('invalid construction vector')
    first = (start - 1 + step - 1) // step
    for offset in range(LIMIT):
        t = first + offset
        if prefer_odd and u % 2 and v % 2 == 0 and t % 2 == 0:
            continue
        p = 1 + t*step
        if gcd(p, SMALL_PRIMES) == 1 and prime_witness(p) is not None:
            if p.bit_length() != 1024 or p != t*u*D + 1-t*v or not modulus**2 > p:
                raise ArithmeticError('prime outside the certified construction range')
            return p, offset
    raise RuntimeError(f'no certified prime in {LIMIT} offsets at vector {index}')


def construct():
    rows = []
    for name, high, low, indices in [('zero', 0, 0, (185, 29)),
                                     ('nonzero', 1, 1, (123, 28))]:
        p, pi = first_prime(3**325, 13*(1 << 1020), indices[0], bool(high))
        q, qi = first_prime(5**224, 15*(1 << 1020), indices[1], bool(high))
        n = p*q
        a, b = nearest(p, D), nearest(q, D)
        x, y = p-a*D, q-b*D
        if not (p < q < 2*p and n.bit_length() == 2048 and
                a*b - nearest(n, D*D) == high and nearest(x*y, D) == low):
            raise ArithmeticError('constructed pair has incorrect shape or carries')
        common = gcd(a, b)
        left, right = b//common, a//common
        distance = left*p + right*q - (1 + isqrt(4*left*right*n-1))
        rows.append(dict(id=f'radix-carry-{name}-2048', n=str(n), expected_factors=[str(p), str(q)],
                         bits=EXPONENT, high_carry=high, low_carry=low,
                         euclidean_vector_indices=list(indices), prime_offsets=[pi, qi],
                         primitive_weights=[str(left), str(right)],
                         primitive_trace_distance=str(distance)))
    if gcd(int(rows[0]['n']), int(rows[1]['n'])) != 1:
        raise ArithmeticError('controls share a prime')
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='compare with the recorded controls')
    parser.add_argument('--verify', action='store_true', help='kernel-check both prime factorizations')
    args = parser.parse_args()
    rows = construct()
    if args.check and json.loads(RECORD.read_text()) != rows:
        raise ValueError('control record differs from the reconstruction')
    if args.verify:
        with TemporaryDirectory() as directory:
            for row in rows:
                proof = Path(directory) / 'Control.lean'
                proof.write_text(render_certificate(int(row['n']), list(map(int, row['expected_factors']))))
                verify_file(proof)
    if not args.check:
        print(json.dumps(rows, indent=2))


if __name__ == '__main__':
    main()
