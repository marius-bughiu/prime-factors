"""Product-only multiplier-six search and a separate reproducible 2048-bit example."""
import argparse
from math import gcd, isqrt
import json

from scripts.factor import prime_witness


def search(n, budget):
    if n < 3 or n % 2 == 0 or budget < 0:
        raise ValueError('expected an odd positive composite candidate and a nonnegative trace budget')
    first = isqrt(24*n-1)+1
    first += 1-first%2
    hits = 0
    for i in range(budget):
        s = first+2*i
        delta = s*s-24*n
        d = isqrt(delta)
        if d*d == delta:
            hits += 1
            f = gcd((s+d)//2, n)
            if 1 < f < n:
                return dict(factor=f, first=first, trace=s, root=d, tests=i+1, squares=hits)
    return dict(factor=None, first=first, trace=None, root=None, tests=budget, squares=hits)


def control():
    """Find two certifiable primes in the prescribed band without testing trace outcomes."""
    unit = 1 << 1024
    grid = 1 << 512
    start = (159*unit//256)//grid
    p_trials = q_trials = 0
    for i in range(start, start+16384):
        p = 1+grid*i
        p_trials += 1
        if prime_witness(p, 2) is None:
            continue
        middle = (3*p//2)//grid
        for j in range(middle+65, middle+256):
            q = 1+grid*j
            q_trials += 1
            if prime_witness(q, 2) is not None:
                return dict(n=str(p*q), factors=[str(p), str(q)], p_trials=p_trials, q_trials=q_trials)
    raise RuntimeError('construction exhausted its fixed grid')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', nargs='?', type=int)
    parser.add_argument('--budget', type=int, default=25001)
    args = parser.parse_args()
    print(json.dumps(control() if args.n is None else search(args.n, args.budget), indent=2))
