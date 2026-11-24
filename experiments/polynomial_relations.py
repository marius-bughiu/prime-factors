"""Compare exact smooth-relation sieves on one interval and on several centered polynomials."""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations
import json
from math import gcd, isqrt
from pathlib import Path

from .exceptional_weights import root_table
from .gap_coverage import primes_through
from .pell_relations import dependency_gcd, insert_parity

SEED = b'polynomial-relations-panel-v1'
PANEL_COUNT, BOUND, RADIUS, BLOCKS = 16, 2048, 512, 64
MODES = ('single', 'square', 'edges')
SEARCH_MODES = MODES + ('centered',)
ROOT = Path(__file__).resolve().parents[1]


@lru_cache(maxsize=1)
def coefficient_primes():
    # For p = 3 mod 4 the proposed modular square root is one modular power.
    return tuple(p for p in primes_through(131071) if p % 4 == 3)


@lru_cache(maxsize=None)
def local_roots_table(p):
    return root_table(p)


def lifted_root(n, p, root, modulus):
    """Lift a unit root from the odd prime p to a specified power of p."""
    m = p
    while m < modulus:
        target = min(m*m, modulus)
        correction = (n-root*root)//m * pow(2*root, -1, target//m)
        root = (root + m*correction) % target
        m = target
    return root


def join_roots(left, m, right, p):
    return left + m*((right-left)*pow(m, -1, p) % p)


def polynomials(n, mode, bound, radius, blocks, base, work):
    """Yield (A, centered B, square part, odd coefficient labels) without using the factors."""
    width = 2*radius+1
    if mode in ('single', 'centered'):
        first = isqrt(n-1)+1
        if mode == 'centered':
            first -= blocks*width//2
        for i in range(blocks):
            yield 1, first + radius + i*width, 1, ()
        return
    target = max(1, isqrt(isqrt(2*n)//radius))
    scale, scale_root = 1, 0
    if target > 65535:
        eligible = next(((p, roots[0]) for _, p, roots in base if p > 2), None)
        if eligible is None:
            work['outcome'] = 'coefficient_budget'
            return
        p, root = eligible
        while target > 65535*scale:
            scale *= p
        scale_root = lifted_root(n, p, root, scale*scale)
    work['square_scale_bits'] = scale.bit_length()
    center = target//scale
    choices = sorted((p for p in coefficient_primes() if p > bound),
                     key=lambda p: (abs(p-center), p))
    pool_size = 2
    while pool_size*(pool_size-1) < blocks:
        pool_size += 1
    need = blocks if mode == 'square' else pool_size
    pool = []
    for p in choices:
        work['coefficient_prime_tests'] += 1
        if n % p == 0:
            if p < n:
                work.update(factor=p, outcome='coefficient_gcd')
                return
            continue
        r = pow(n, (p+1)//4, p)
        if r*r % p == n % p:
            pool.append((p, r))
            if len(pool) == need:
                break
    if len(pool) < need:
        work['outcome'] = 'coefficient_budget'
        return
    work['coefficient_primes'] = len(pool)
    if mode == 'square':
        def local():
            for p, r in pool:
                yield p*p, lifted_root(n, p, r, p*p), scale*p, ()
    else:
        def local():
            for (i,(p,r)), (j,(q,s)) in combinations(enumerate(pool), 2):
                for root in (s, -s):
                    yield p*q, join_roots(r, p, root, q), scale, (i,j)
    for count, (mod, root, square_part, edge) in enumerate(local()):
        if count >= blocks:
            return
        a = mod*scale*scale
        b = root if scale == 1 else join_roots(scale_root, scale*scale, root, mod)
        if 2*b > a:
            b -= a
        yield a, b, square_part, edge


def sieve(n, a, b, radius, base, work):
    """Produce all B-smooth signed polynomial values and their exact parity vectors."""
    c, rem = divmod(b*b-n, a)
    if rem:
        raise ArithmeticError('coefficient does not divide B squared minus the product')
    width = 2*radius+1
    y = a*radius*radius-2*b*radius+c
    step = a*(1-2*radius)+2*b
    values = []
    for _ in range(width):
        values.append(y)
        y += step
        step += 2*a
    remainders = list(map(abs, values))
    parities = [int(y < 0) for y in values]
    for bit, p, roots in base:
        if a % p:
            inv = pow(a, -1, p)
            starts = [(radius+(r-b)*inv) % p for r in roots]
        else:
            starts = [(radius-c*pow(2*b, -1, p)) % p]
        work['sieve_progressions'] += len(starts)
        for first in starts:
            for j in range(first, width, p):
                work['sieve_marks'] += 1
                v = remainders[j]
                while v % p == 0:
                    v //= p
                    parities[j] ^= bit
                    work['prime_divisions'] += 1
                remainders[j] = v
    return [(i-radius, y, parities[i]) for i,y in enumerate(values) if remainders[i] == 1]


def analyze(n, rows, metadata, base_bits, policy):
    """Check a basis of the permitted square products; keep counting dimensions after a split."""
    pivots = {}
    work = dict(dependencies=0, gcd_tests=0, factor=None, first_position=None,
                first_block=None, chosen_rows=0, odd_coefficients=0, odd_polynomials=0)
    for i, (row, info) in enumerate(zip(rows, metadata)):
        parity, block, edge_number, edge = info
        if policy == 'edges':
            for j in edge:
                parity ^= 1 << (base_bits+j)
        elif policy == 'coefficient':
            parity ^= 1 << (base_bits+edge_number)
        elif policy == 'polynomial':
            parity ^= 1 << (base_bits+block)
        mask = insert_parity(pivots, parity, 1 << i)
        if mask is None:
            continue
        work['dependencies'] += 1
        if work['factor'] is not None:
            continue
        divisor, selected = dependency_gcd(n, rows, mask)
        work['gcd_tests'] += 1
        if 1 < divisor < n:
            blocks = Counter()
            edges = Counter()
            for j in range(i+1):
                if (mask >> j) & 1:
                    blocks[metadata[j][1]] += 1
                    edges[metadata[j][2]] += 1
            work.update(factor=divisor, first_position=row[0], first_block=block+1,
                        chosen_rows=len(selected), odd_polynomials=sum(x%2 for x in blocks.values()),
                        odd_coefficients=sum(x%2 for x in edges.values()) if edge else 0)
    return work


def search(n, mode, bound=BOUND, radius=RADIUS, blocks=BLOCKS, *, policy=None):
    if n <= 2 or n % 2 == 0 or mode not in SEARCH_MODES or min(radius, blocks) <= 0 or bound < 2:
        raise ValueError('expected an odd product, a known search mode and positive sieve dimensions')
    policies = ('edges', 'coefficient', 'polynomial') if mode == 'edges' else ('base',)
    if policy is not None:
        if policy not in policies:
            raise ValueError('unsupported parity policy for this coefficient mode')
        policies = (policy,)
    work = dict(factor=None, outcome='no_split', blocks=0, positions=0, base_prime_tests=0,
                base_size=0, coefficient_prime_tests=0, coefficient_primes=0, square_scale_bits=0,
                sieve_progressions=0, sieve_marks=0, prime_divisions=0, smooth_rows=0,
                occupied_blocks=0, policies={})
    root = isqrt(n)
    if root*root == n:
        return dict(work, factor=root, outcome='square')
    base = []
    for p in primes_through(bound):
        work['base_prime_tests'] += 1
        if n % p == 0:
            if p < n:
                return dict(work, factor=p, outcome='base_gcd')
            continue
        roots = local_roots_table(p)[n % p]
        if roots:
            base.append((1 << (len(base)+1), p, roots))
    work['base_size'] = len(base)
    rows, metadata = [], []
    width = 2*radius+1
    for block, (a,b,square_part,edge) in enumerate(polynomials(n, mode, bound, radius, blocks, base, work)):
        work['blocks'] += 1
        work['positions'] += width
        smooth = sieve(n, a, b, radius, base, work)
        work['occupied_blocks'] += int(bool(smooth))
        inverse = pow(square_part, -1, n)
        for x, value, parity in smooth:
            position = block*width+x+radius+1
            norm = (a//(square_part*square_part))*value
            lifted = (a*x+b)*inverse % n
            if (lifted*lifted-norm) % n:
                raise ArithmeticError('invalid reduced polynomial relation')
            rows.append((position, norm, lifted))
            metadata.append((parity, block, block//2, edge))
    work['smooth_rows'] = len(rows)
    if work['factor'] is not None or work['outcome'] == 'coefficient_budget':
        return work
    for policy in policies:
        work['policies'][policy] = analyze(n, rows, metadata, len(base)+1, policy)
    factor = work['policies'][policies[0]]['factor']
    return dict(work, factor=factor, outcome='relation' if factor else 'no_split')


def panel():
    from .crt_holdout import draw_sample
    cases = []
    for attempt, n, expected in draw_sample(SEED, PANEL_COUNT):
        runs = {}
        for mode in SEARCH_MODES:
            work = search(n, mode)
            f = work.pop('factor')
            factors = [] if f is None else sorted((f,n//f))
            if factors and (n%f or factors != expected):
                raise ArithmeticError('independently generated factors disagree')
            for stats in work['policies'].values():
                divisor = stats['factor']
                if divisor is not None and divisor not in expected:
                    raise ArithmeticError('invalid divisor from a restricted relation')
                stats['factor'] = str(divisor) if divisor else None
            runs[mode] = dict(work=work, factors=list(map(str,factors)), remaining=[] if f else [str(n)])
        centered = runs.pop('centered')
        cases.append(dict(attempt=attempt,n=str(n),expected_factors=list(map(str,expected)),
                          methods=runs, centered_single_sensitivity=centered))
    return dict(seed=SEED.decode(),count=PANEL_COUNT,bound=BOUND,radius=RADIUS,blocks=BLOCKS,cases=cases)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', nargs='?', type=int)
    parser.add_argument('--mode', choices=SEARCH_MODES, default='edges')
    parser.add_argument('--policy', choices=('base','edges','coefficient','polynomial'))
    parser.add_argument('--bound', type=int, default=BOUND)
    parser.add_argument('--radius', type=int, default=RADIUS)
    parser.add_argument('--blocks', type=int, default=BLOCKS)
    parser.add_argument('--panel', action='store_true')
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    if args.panel:
        report = panel()
        if args.verify:
            from .crt_holdout import verify_cases
            verify_cases(report['cases'], ROOT/'build'/'polynomial-relations-panel')
        (ROOT/'research'/'polynomial-relations-panel.json').write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps({mode:sum(bool(case['methods'][mode]['factors']) for case in report['cases'])
                          for mode in MODES}))
    elif args.n is not None:
        print(json.dumps(search(args.n, args.mode, args.bound, args.radius, args.blocks, policy=args.policy)))
    else:
        parser.error('supply an integer or --panel')
