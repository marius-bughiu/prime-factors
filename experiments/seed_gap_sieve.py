"""Enumerate weighted differences of squares after sieving the multipliers for each gap."""
from argparse import ArgumentParser
from bisect import bisect_right
import json
from math import gcd, isqrt, prod

ODD_PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29)


def components(last_prime):
    if last_prime not in ODD_PRIMES:
        raise ValueError('unsupported final wheel prime')
    return (16,) + tuple(p for p in ODD_PRIMES if p <= last_prime)


def candidate_bound(k, last_prime):
    """Uniform bound for unit inputs; no residue table needs to be built."""
    if k < 0:
        raise ValueError('negative multiplier budget')
    mods = components(last_prime)
    modulus = prod(mods)
    entries = 4 * prod((p + 1)//2 for p in mods[1:])
    d = max(1, isqrt(k // entries))
    cap = 5*k*entries // (3*modulus) + d*entries + k//d
    # Counting every (h,v) without modular pruning also bounds the total.
    return modulus, entries, min(5*k//3, cap)


def square_classes(n, mods):
    """Build N-inverse times the distinct squares by CRT, including zero."""
    residues, modulus = [0], 1
    for m in mods:
        inverse = pow(modulus, -1, m)
        n_inverse = pow(n, -1, m)
        scaled = {i*i*n_inverse % m for i in range(m)}
        residues = [r + modulus*((s-r)*inverse % m) for r in residues for s in scaled]
        modulus *= m
    return modulus, sorted(residues)


def allowed(maximum, shift, modulus, residues):
    """Yield h in [1,maximum] for which h+shift is in the sorted cyclic set."""
    stop = shift + maximum
    for block in range(shift//modulus, stop//modulus + 1):
        base = block*modulus
        first = bisect_right(residues, shift-base)
        last = bisect_right(residues, stop-base)
        for i in range(first, last):
            yield base+residues[i]-shift


def search(n, max_norm, last_prime=13):
    if n <= 2 or n % 2 == 0 or max_norm < 1:
        raise ValueError('expected an odd input above two and a positive norm limit')
    mods = components(last_prime)
    k = (min(max_norm, (n-1)//2) - 1)//2
    work = dict(factor=None, outcome='no_split', multiplier_limit=k, modulus=1,
                entries=0, gaps=0, square_tests=0, multiplier=None, gap=None)
    if k == 0:
        return work
    for m in mods:
        d = gcd(m, n)
        if 1 < d < n:
            return dict(work, factor=d, outcome='wheel_gcd')
    # A prime test input may itself be a wheel prime.
    mods = tuple(m for m in mods if gcd(m,n) == 1)
    modulus, residues = square_classes(n, mods)
    inverse = pow(n, -1, modulus)
    work.update(modulus=modulus, entries=len(residues))
    for v in range(1, isqrt(k)+1):
        work['gaps'] += 1
        vv = v*v
        shift = vv*inverse % modulus
        for h in allowed(k//vv, shift, modulus, residues):
            work['square_tests'] += 1
            candidate = h*n+vv
            u = isqrt(candidate)
            if u*u == candidate:
                factor = gcd(u-v, n)
                if 1 < factor < n:
                    return dict(work, factor=factor, outcome='gap', multiplier=h, gap=str(v))
    return work


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--max-norm', type=int, required=True)
    parser.add_argument('--last-prime', type=int, default=13, choices=ODD_PRIMES)
    args = parser.parse_args()
    print(json.dumps(search(args.n, args.max_norm, args.last_prime)))
