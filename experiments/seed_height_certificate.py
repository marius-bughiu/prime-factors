"""Bound the smallest row in any short square pair, using two supplied prime factors."""
import argparse
import json
from math import gcd
from pathlib import Path

from .fraction_chains import euclidean_pairs


def crossed_factors():
    """Read the established control and its two separately certified prime labels."""
    bench = Path(__file__).resolve().parents[1] / 'benchmarks'
    def row(filename, identifier):
        return next(r for r in json.loads((bench / filename).read_text()) if r['id'] == identifier)
    n = int(row('rational-squares.json', 'rational-fraction-2048')['n'])
    primes = [int(x) for filename, identifier in (
        ('line-powers.json', 'dickson-square-1-2048'),
        ('predecessor-square.json', 'predecessor-square-2048'))
        for x in row(filename, identifier)['factors'] if n % int(x) == 0]
    if len(primes) != 2 or primes[0]*primes[1] != n:
        raise ValueError('the factor labels no longer match the crossed control')
    return sorted(primes)


def certificate(p, q):
    """The caller supplies distinct, established odd primes p < q < 2p."""
    if not 2 < p < q < 2*p or not p % 2 or not q % 2 or gcd(p, q) != 1:
        raise ValueError('expected two distinct balanced odd prime labels')
    n = p*q
    r = (1 - 2*p*pow(p, -1, q)) % n
    if r % p != 1 or r % q != q-1:
        raise ArithmeticError('incorrect mixed root')
    chain = list(euclidean_pairs(n, r))
    w, u, v = min((abs(num)*den, abs(num), den) for _, num, den in chain)
    if 2*w >= n or gcd(u, v) != 1 or gcd(w, n) != 1 or (u*u-v*v) % n:
        raise ArithmeticError('expected a primitive short mixed-root fraction')
    lower = 2*w*w // n + 1
    # A divisor of w transfers weight between two fractions. A bounded search
    # gives an attainable upper bound even when the full factorization of w is unknown.
    cap = min(65536, (n-1) // (2*w))
    d = next(d for d in range(cap, 0, -1) if w % d == 0)
    upper = w // d
    a = gcd(upper, u*u)
    b = upper // a
    c, e = v*v // b, u*u // a
    source = a*pow(b, -1, n) % n
    if (a*e, b*c, a*b, c*e) != (u*u, v*v, upper, w*d):
        raise ArithmeticError('invalid redistribution of the cross products')
    if (2*max(a*b, c*e) >= n or (a,b) == (c,e) or (source*e-c) % n
            or gcd(a,b) != 1 or gcd(c,e) != 1 or gcd(source*b*e-w, n) not in (p,q)):
        raise ArithmeticError('the attained upper bound did not give a valid short pair')
    return dict(n=str(n), mixed_root=str(r), euclidean_steps=len(chain),
                min_product=str(w), min_coordinates=[str(u), str(v)],
                lower=str(lower), upper=str(upper), divisor=d,
                source=str(source), fractions=[[str(a), str(b)], [str(c), str(e)]])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--primes', nargs=2, type=int, metavar=('P', 'Q'),
                        help='two previously certified primes (default: the crossed control)')
    args = parser.parse_args()
    print(json.dumps(certificate(*(args.primes or crossed_factors())), indent=2))
