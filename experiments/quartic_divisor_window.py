"""Check a bounded divisor progression with a degree-four auxiliary polynomial.

The lattice is the univariate unknown-divisor small-root construction. The
search verifies both divisibilities and the strict coefficient bound in integers.
"""

import argparse
from collections import Counter
import json
from math import gcd

from experiments.arbitrary_divisor_window import quartile_center
from experiments.norm_auxiliary import integer_roots, reduced_basis
from scripts.factor import primes_through


def odd_quartile_center(n):
    """First odd integer at or above the lower quartile of the equal-width range."""
    return quartile_center(n) | 1


def evaluate(coefficients, x):
    value = 0
    for coefficient in reversed(coefficients):
        value = value*x+coefficient
    return value


def jet_basis(n, t):
    """Ascending coefficients of N², N(x−t), and x^j(x−t)² for j=0,1,2."""
    return [
        [n*n, 0, 0, 0, 0],
        [-n*t, n, 0, 0, 0],
        [t*t, -2*t, 1, 0, 0],
        [0, t*t, -2*t, 1, 0],
        [0, 0, t*t, -2*t, 1],
    ]


def checked_height(n, t, radius, coefficients):
    """Return the coefficient bound, rejecting a zero polynomial or invalid jets."""
    if len(coefficients) != 5 or not any(coefficients):
        raise ValueError('expected five coefficients of a nonzero polynomial')
    derivative = [i*coefficients[i] for i in range(1,5)]
    if evaluate(coefficients,t) % (n*n) or evaluate(derivative,t) % n:
        raise ArithmeticError('the chosen polynomial failed a required divisibility')
    return sum(abs(coefficient)*radius**i for i,coefficient in enumerate(coefficients))


def rootless_prime(coefficients, limit, work):
    """Find a small prime whose residue table can independently certify an exclusion."""
    for p in primes_through(limit):
        work['moduli_tested'] += 1
        local = [coefficient%p for coefficient in coefficients]
        for x in range(p):
            work['modular_evaluations'] += 1
            if evaluate(local,x) % p == 0:
                break
        else:
            return p
    return None


def search(n, center, radius, *, stride=2, modulus_limit=97):
    """Return every divisor c+s*x in this progression for |x|≤W if certified.

    A short integer relation is required. A missed length bound returns partial.
    Stride one covers the interval. A stride-two odd progression also covers
    every possible divisor in its enclosing interval when N is odd.
    """
    lower, upper = center-stride*radius, center+stride*radius
    if n < 2 or min(stride,radius,lower) < 1 or gcd(stride,n) != 1 or modulus_limit < 0:
        raise ValueError('expected N≥2, coprime positive stride, positive radius and lower bound')
    anchor = -center*pow(stride,-1,n) % n
    if 2*anchor > n:
        anchor -= n
    if (center+stride*anchor) % n:
        raise ArithmeticError('the public anchor failed its congruence')

    work = Counter(dict(lll_calls=0, lll_reductions=0, lll_swaps=0, integer_root_nodes=0,
                        divisor_tests=0, moduli_tested=0, modular_evaluations=0))
    scales = [radius**i for i in range(5)]
    basis = jet_basis(n,anchor)
    scaled = [[a*b for a,b in zip(row,scales)] for row in basis]
    _, reduced = reduced_basis(scaled,work,initial_coefficients=basis)
    coefficients = min(reduced,key=lambda row:sum(abs(a)*b for a,b in zip(row,scales)))
    height = checked_height(n,anchor,radius,coefficients)
    verified = height < lower*lower
    covers_interval = stride == 1 or (stride == 2 and n%2 == 1 and center%2 == 1)
    roots, hits = [], []
    modulus = None
    if verified:
        roots = sorted(integer_roots(coefficients,-radius,radius,work))
        for x in roots:
            if not -radius <= x <= radius or evaluate(coefficients,x):
                raise ArithmeticError('invalid proposed integer root')
            divisor = center+stride*x
            work['divisor_tests'] += 1
            cofactor, remainder = divmod(n,divisor)
            if not remainder:
                hits.append(dict(offset=x,divisor=divisor,cofactor=cofactor))
        if not roots and modulus_limit >= 2:
            modulus = rootless_prime(coefficients,modulus_limit,work)

    progression_excluded = verified and not hits
    excluded = covers_interval and progression_excluded
    if not verified:
        status = 'partial'
    elif hits:
        status = 'divisors_found'
    else:
        status = 'excluded' if covers_interval else 'progression_excluded'
    return dict(n=n,center=center,radius=radius,stride=stride,lower=lower,upper=upper,
                interval_size=upper-lower+1, progression_size=2*radius+1, covers_interval=covers_interval,
                anchor=anchor,coefficients=coefficients,height=height,height_bound=lower*lower,
                relation_verified=verified, anchor_inversions=1, basis_dimension=5, rows_compared=len(reduced),
                jet_checks=2, modulus_limit=modulus_limit, rootless_modulus=modulus,
                roots=roots,hits=hits,divisors=[h['divisor'] for h in hits],**work,
                progression_excluded=progression_excluded,excluded=excluded,status=status)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int)
    parser.add_argument('radius',type=int)
    location = parser.add_mutually_exclusive_group(required=True)
    location.add_argument('--center',type=int)
    location.add_argument('--odd-quartile',action='store_true')
    parser.add_argument('--stride',type=int,default=2)
    parser.add_argument('--modulus-limit',type=int,default=97)
    args = parser.parse_args()
    center = odd_quartile_center(args.n) if args.odd_quartile else args.center
    print(json.dumps(search(args.n,center,args.radius,stride=args.stride,
                            modulus_limit=args.modulus_limit),indent=2))
