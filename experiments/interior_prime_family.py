"""Product-only multiplier-six search and a separate reproducible 2048-bit example."""
import argparse
from itertools import islice
from math import gcd, isqrt
import json

from scripts.factor import prime_witness


def search(n, budget):
    if n < 3 or n % 2 == 0 or budget < 0:
        raise ValueError('expected an odd positive composite candidate and a nonnegative trace budget')
    first = isqrt(24*n-1)+1
    first += 1-first%2
    return _scan(n, first, range(first, first+2*budget, 2))


def search_blocks(n, blocks):
    """Test residues 1 and 5 modulo 6 in blocks aligned with the gap theorem."""
    if n <= 1 or gcd(n, 6) != 1 or blocks < 0:
        raise ValueError('expected a product coprime to six and a nonnegative block count')
    first = isqrt(24*n-1)+1
    return _scan(n, first, _unit_labels(first, blocks))


def _unit_labels(first, blocks):
    base = first - first%6
    return (s for low in range(base, base+6*blocks, 6)
            for s in (low+1, low+5) if s >= first)


def search_units(n, budget):
    """Give the unit-residue search an exact budget of square tests."""
    if n <= 1 or gcd(n, 6) != 1 or budget < 0:
        raise ValueError('expected a product coprime to six and a nonnegative square-test budget')
    first = isqrt(24*n-1)+1
    labels = _unit_labels(first, (budget+1)//2+1)
    return _scan(n, first, islice(labels, budget))


def _scan(n, first, labels):
    hits = 0
    tests = 0
    for tests, s in enumerate(labels, 1):
        delta = s*s-24*n
        d = isqrt(delta)
        if d*d == delta:
            hits += 1
            f = gcd((s+d)//2, n)
            if 1 < f < n:
                return dict(factor=f, first=first, trace=s, root=d, tests=tests, squares=hits)
    return dict(factor=None, first=first, trace=None, root=None, tests=tests, squares=hits)


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
    bound = parser.add_mutually_exclusive_group()
    bound.add_argument('--budget', type=int, default=25001)
    bound.add_argument('--blocks', type=int, help='test two possible labels per block of six')
    bound.add_argument('--unit-budget', type=int, help='exact square-test budget on labels coprime to six')
    args = parser.parse_args()
    if args.n is None:
        result = control()
    elif args.unit_budget is not None:
        result = search_units(args.n, args.unit_budget)
    elif args.blocks is None:
        result = search(args.n, args.budget)
    else:
        result = search_blocks(args.n, args.blocks)
    print(json.dumps(result, indent=2))
