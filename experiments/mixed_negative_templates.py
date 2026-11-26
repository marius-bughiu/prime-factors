"""Classify primitive (1,2) negative-norm templates with 2a and 2b dividing 24.

Run `python3 -m experiments.mixed_negative_templates` for the finite classification,
small prime-pair census, and product-only Fermat search spans on the large controls.
"""

from itertools import combinations, product
import json
from math import gcd, isqrt
from pathlib import Path

from .gap_coverage import primes_through
from .mixed_negative_norms import full_counts, squarefree_kernels


ROOT = Path(__file__).resolve().parents[1]
UNITS = tuple(r for r in range(24) if gcd(r, 6) == 1)
SCALES = tuple(a for a in range(1, 13) if 24 % (2*a) == 0)


def possible_templates(residue):
    """The coarse geometric filter is necessary; its only survivor works at every balanced ratio."""
    result = []
    for a, b in product(SCALES, repeat=2):
        if gcd(a, b) != 1 or a == b:
            continue
        delta = b*b - 2*a*a
        sign = 1 if delta > 0 else -1
        for u in range(1, abs(delta) + 1):
            v, remainder = divmod(abs(delta), u)
            if remainder or 2*max(u, v) >= 3*b + 4*a:
                continue
            if (u + sign*v*residue) % (2*b) or (u - sign*v*residue) % (2*a):
                continue
            # t=|up+sign*vq|/(2b). Positivity of N-t² on 1≤q/p≤2
            # follows at both endpoints because the negative of this quadratic is concave.
            covers = all((u + sign*v*r)**2 < 4*b*b*r for r in (1, 2))
            result.append({'a': a, 'b': b, 'u': u, 'v': v, 'all_balanced_ratios': covers})
    return result


def schedule(n):
    """Odd t with 9t² ≥ N and 8t² ≤ N. Zero cost means the template is inapplicable."""
    if n <= 1:
        raise ValueError('expected n>1')
    if n % 12 != 5:
        return None
    lower = isqrt(n-1)//3 + 1
    first = lower + (lower % 2 == 0)
    last = isqrt(n//8)
    if last % 2 == 0:
        last -= 1
    return first, last, max(0, (last-first)//2 + 1)


def scan(n, cap):
    if cap < 0:
        raise ValueError('the visit cap must be nonnegative')
    bounds = schedule(n)
    if bounds is None:
        return {'outcome': 'inapplicable', 'visited': 0, 'remaining': 0}
    first, _, total = bounds
    for i in range(min(cap, total)):
        t = first + 2*i
        difference = 9*t*t - n
        y = isqrt(difference)
        if y*y == difference and y % 2 == 0 and 1 < 3*t-y:
            p, q = 3*t-y, 3*t+y
            if p*q != n:
                raise ArithmeticError('recovered factors fail the product check')
            return {'outcome': 'split', 'factors': [p, q], 't': t, 's': y//2,
                    'visited': i+1, 'remaining': total-i-1}
    return {'outcome': 'exhausted' if cap >= total else 'capped', 'visited': min(total, cap),
            'remaining': max(0, total-cap)}


def census(bits, archived):
    lower = 1 << (bits-1)
    primes = [p for p in primes_through(2*lower-1) if p >= lower]
    pairs = [(p, q) for p, q in combinations(primes, 2) if p*q >= 2*lower**2]
    if len(pairs) != archived['total']['products']:
        raise ArithmeticError('prime-pair population changed')
    selected = visits = 0
    for p, q in pairs:
        n = p*q
        bounds = schedule(n)
        if bounds is None:
            continue
        result = scan(n, bounds[2])
        if result.get('factors') != [p, q]:
            raise ArithmeticError('template failed on eligible prime pair')
        t, s = result['t'], result['s']
        d, e = n-t*t, 2*n-s*s
        g = gcd(d, e)
        if (d, e, gcd(n, t*s-6*g), gcd(n, t*s+6*g)) != (4*g, 9*g, q, p):
            raise ArithmeticError('failed the unequal square match or its signed gcds')
        selected += 1
        visits += result['visited']
    missing = int(archived['examples']['no_unequal_match']['n'])
    work, _ = full_counts(missing, squarefree_kernels(2*missing))
    if work['mixed_unequal_matches'] or schedule(missing) is not None:
        raise ArithmeticError('recorded counterexample did not reproduce')
    observed = archived['total']['mixed_unequal_split_products']
    return {'bits_per_prime': bits, 'total': len(pairs), 'template_splits': selected,
            'square_tests_to_hits': visits, 'other_unequal_splits_from_archive': observed-selected,
            'rechecked_no_unequal_match': missing, 'counterexample_mod_24': missing % 24}


if __name__ == '__main__':
    archived = json.loads((ROOT/'research/mixed-negative-norms.json').read_text())
    controls = json.loads((ROOT/'benchmarks/arbitrary-divisor-window.json').read_text())
    report = {'classes': {r: possible_templates(r) for r in UNITS},
              'census': [census(row['factor_bits'], row) for row in archived['exhaustive']],
              'unvisited_controls': {}}
    for case in controls:
        if case['id'] in ('arbitrary-divisor-window-fresh-2048', 'arbitrary-divisor-window-crossed-2048'):
            n = int(case['n'])
            report['unvisited_controls'][case['id']] = {'mod_24': n % 24, **scan(n, 0)}
    print(json.dumps(report, indent=2))
