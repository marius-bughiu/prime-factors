"""Recover factors of P_i(t) P_j(t), where P_i(t)=i²*t+2*i+1, from the product.

The public ratio floor(sqrt(N)) / (N-floor(sqrt(N))²) suggests reduced index
directions via ordinary continued fractions. Each accepted split reconstructs
positive integer parameters and verifies the product exactly. Primality is
checked separately by the repository certificate generator.
"""

import argparse
import json
from itertools import islice
from math import isqrt


def convergents(numerator, denominator):
    old_u, u = 0, 1
    old_v, v = 1, 0
    while denominator:
        digit, remainder = divmod(numerator, denominator)
        old_u, u = u, digit*u + old_u
        old_v, v = v, digit*v + old_v
        yield u, v
        numerator, denominator = denominator, remainder


def search(n, max_convergents=None):
    if n < 2 or (max_convergents is not None and max_convergents < 0):
        raise ValueError("expected N >= 2 and a nonnegative optional convergent limit")
    s = isqrt(n)
    residual = n-s*s
    result = dict(factor=None, cofactor=None, convergents=0, square_tests=0,
                  direction_tests=0, max_convergents=max_convergents)
    for u, v in islice(convergents(s, residual), max_convergents):
        result['convergents'] += 1
        if u == 0 or residual % v:
            continue
        gap = isqrt(v)
        result['square_tests'] += 1
        if gap*gap != v:
            continue
        total = isqrt(4*u+v)
        result['square_tests'] += 1
        if total*total != 4*u+v or (total-gap) % 2:
            continue
        a, b = (total-gap)//2, (total+gap)//2
        if a < 1:
            continue
        result['direction_tests'] += 1
        constant = s-u*(residual//v)
        if constant <= 1:
            continue
        disc = total*total + 4*u*(constant-1)
        root = isqrt(disc)
        result['square_tests'] += 1
        if root*root != disc:
            continue
        g, leftover = divmod(root-total, 2*u)
        if g < 1 or leftover or residual % (g*g*v):
            continue
        t = 1+residual//(g*g*v)
        i, j = g*a, g*b
        p, q = i*i*t+2*i+1, j*j*t+2*j+1
        if 1 < p < q and p*q == n:
            result.update(factor=p, cofactor=q, a=a, b=b, scale=g, parameter=t)
            break
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--max-convergents', type=int)
    args = parser.parse_args()
    print(json.dumps(search(args.n, args.max_convergents)))
