"""Search primitive offset fractions by combining locally possible projective slopes."""

import argparse
from itertools import product
import json
from math import gcd, isqrt, prod
from pathlib import Path
from tempfile import TemporaryDirectory

from experiments.complete_offset_search import slot_count
from experiments.continued_square import convergents
from experiments.offset_crt_wheel import choose_wheel
from scripts.factor import primes_through, render_certificate, verify_file

# This product exceeds twice the enclosing rectangle area for every 2048-bit input.
WHEEL = tuple(p for p in primes_through(743) if p >= 5)


def local_slopes(p, n, t):
    """Finite residues j/k of square discriminant, followed by the line k=0."""
    # (r+2T-z)(r+2T+z)=4N, so each finite slope is x+N/x-2T for x!=0.
    finite = {(x+n*pow(x, -1, p)-2*t) % p for x in range(1, p)}
    return (*sorted(finite), None)


def reconstruct(primes, slopes, j_limit, k_limit):
    """Return the only primitive box point consistent with one projective CRT tuple."""
    infinity = modulus = 1
    residue = 0
    if len(primes) != len(slopes):
        raise ValueError('each prime requires one slope')
    for p, slope in zip(primes, slopes):
        if slope is None:
            infinity *= p
        else:
            residue += modulus*((slope-residue)*pow(modulus, -1, p) % p)
            modulus *= p
    if infinity > k_limit:
        return None, 0
    a = residue*infinity % modulus
    steps = 0
    for w, v in convergents(a, modulus):
        steps += 1
        k = v*infinity
        if k > k_limit:
            break
        j = a*v-w*modulus
        if 1 <= j <= j_limit and gcd(j,k) == 1:
            return (j,k), steps
    return None, steps


def search(n, max_tuples, *, exhaust=False, optimize_wheel=False):
    """Take only N and a finite tuple budget. Count all unchecked tuples, even after a split."""
    if not 4 <= n < 2**2048 or max_tuples < 0:
        raise ValueError('expected 4 <= N < 2^2048 and a nonnegative tuple budget')
    t = isqrt(n)
    h = n-t*t
    j_limit = isqrt(4*h//3)
    k_limit = t*j_limit//h+1 if h else 0
    result = dict(status='partial', factor=None, remaining=n, primes=[], total_tuples=0, visited_tuples=0,
                  unchecked_tuples=0, convergents=0, reconstructed=0, square_tests=0, proper_hits=0,
                  first_hit=None, raw_slots=slot_count(t,h,j_limit)[0] if h else 0)
    if not h:
        result.update(status='square', factor=t, remaining=t)
        return result
    if optimize_wheel:
        plan = choose_wheel(n, j_limit, k_limit)
        result['wheel_work'] = plan['work']
        if plan['factor'] is not None:
            p = plan['factor']
            result.update(status='trial-split', factor=p, remaining=n//p)
            return result
        primes = list(plan['primes'])
        modulus = plan['modulus']
        result['baseline_tuples'] = plan['baseline_tuples']
    else:
        modulus = 1
        primes = []
        for p in WHEEL:
            if p == n:
                continue
            if n%p == 0:
                result.update(status='trial-split', factor=p, remaining=n//p)
                return result
            primes.append(p)
            modulus *= p
            if modulus > 2*j_limit*k_limit:
                break
    if modulus <= 2*j_limit*k_limit:
        raise ArithmeticError('target wheel missed the rational reconstruction threshold')
    allowed = [local_slopes(p,n,t) for p in primes]
    total = prod(map(len, allowed))
    if optimize_wheel and total != plan['total_tuples']:
        raise ArithmeticError('local alphabets disagree with the selected wheel cost')
    result.update(primes=primes, total_tuples=total, unchecked_tuples=total)
    for slopes in product(*allowed):
        if result['visited_tuples'] == max_tuples:
            break
        result['visited_tuples'] += 1
        result['unchecked_tuples'] -= 1
        pair, steps = reconstruct(primes, slopes, j_limit, k_limit)
        result['convergents'] += steps
        if pair is None:
            continue
        j, k = pair
        if k > t*j//h+1:
            continue
        result['reconstructed'] += 1
        delta = j*j+4*k*(t*j-h*k)
        if delta < 0:
            continue
        result['square_tests'] += 1
        d = isqrt(delta)
        if d*d != delta:
            continue
        f = gcd(n,(j+2*t*k-d)//2)
        if 1 < f < n:
            result['proper_hits'] += 1
            if result['first_hit'] is None:
                result.update(status='split',factor=f,remaining=n//f,first_hit=[j,k])
            if not exhaust:
                break
    if result['factor'] is None and not result['unchecked_tuples']:
        result['status'] = 'exhausted'
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--max-tuples', type=int, default=1024)
    parser.add_argument('--exhaust', action='store_true', help='continue within budget after the first split')
    parser.add_argument('--optimize-wheel', action='store_true', help='minimize tuple count within a bounded prime menu')
    parser.add_argument('--verify', action='store_true', help='ask Lean to check both factors are prime and multiply to N')
    args = parser.parse_args()
    result = search(args.n, args.max_tuples, exhaust=args.exhaust, optimize_wheel=args.optimize_wheel)
    if args.verify and result['factor'] is not None:
        with TemporaryDirectory() as temp:
            certificate = Path(temp)/'OffsetCRTFactorization.lean'
            certificate.write_text(render_certificate(args.n, [result['factor'],result['remaining']]))
            verify_file(certificate)
        result['primes_kernel_checked'] = True
    print(json.dumps(result, indent=2))
