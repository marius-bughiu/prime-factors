"""Allocate fifteen weighted labels from the leading interval widths alone."""
from math import gcd, isqrt

from .shared_multiplier_prefix import UNITS24

PRECISION = 2**64


def step(a, b, r):
    g = gcd(a+b*r, 24)
    return 24//sum(gcd(j,24) == g for j in range(24))


def lower_score(a, b, r, count):
    # Floor of 2^64 times (b/a^3)^(1/4)*sqrt(step*count).
    value = PRECISION**4*b*(step(a,b,r)*count)**2//a**3
    return isqrt(isqrt(value))


def choose(r):
    scores = [lower_score(3,2,r,h)+lower_score(7,5,r,15-h) for h in range(16)]
    winner = max(range(16), key=lambda h: (scores[h], -h))
    # Each exact score lies in [low, low+2). This checks strict superiority
    # for these eight public residues without comparing floating point numbers.
    if any(scores[h]+2 > scores[winner] for h in range(16) if h != winner):
        raise ArithmeticError('fixed-point intervals did not certify a unique winner')
    return winner, 15-winner


ALLOCATION = {r: choose(r) for r in UNITS24}

if __name__ == '__main__':
    for r, (h, k) in ALLOCATION.items():
        print(r, step(3,2,r), step(7,5,r), h, k)
