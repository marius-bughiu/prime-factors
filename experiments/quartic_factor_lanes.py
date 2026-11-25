"""One polynomial per unordered pair of factor remainders. The default degree is four."""

import argparse
from collections import Counter
import json
from math import comb, gcd, isqrt

from .midpoint_weights import residue_pairs, smooth_radix
from .norm_auxiliary import integer_roots, reduced_basis
from .powered_order import prime_powers


def parameters(n, power=2):
    bound = isqrt(2*n)
    if power != 2:
        if power < 1:
            raise ValueError('expected a positive factor power')
        size = 2*power+1
        # Bound the scaled LLL vector using bits without forming powers of N of degree O(power²).
        bits = (size-1).bit_length()*size + power*size + (bound*bound).bit_length()*power*(power+1)
        exponent = bits//(2*power*size)+1
        return bound, smooth_radix(n, 1 << exponent)
    threshold = 6**5 * bound**6
    low, high = 1, 1 << ((threshold.bit_length()+9)//10)
    while low+1 < high:
        mid = (low+high)//2
        if mid**10 < threshold:
            low = mid
        else:
            high = mid
    return bound, smooth_radix(n, high)


def lane_basis(n, u, radix, power=2):
    """Triangular basis annihilating all Taylor coefficients below the chosen degree."""
    degree = 2*power
    factors = [n**max(power-j, 0) for j in range(degree+1)]
    bounds = [radix**(degree-i) for i in range(degree)]
    column = [[comb(k, i)*factors[k]*u**(k-i) % m if k >= i else 0 for k in range(degree+1)]
              for i, m in enumerate(bounds)]
    inverse = [pow(factors[i], -1, m) for i,m in enumerate(bounds)]
    rows = []
    for j in range(degree+1):
        row = [0]*(degree+1)
        row[j] = bounds[j] if j < degree else 1
        for i in reversed(range(j)):
            m = bounds[i]
            entry = -sum(row[k]*column[i][k] for k in range(i+1, j+1))*inverse[i] % m
            row[i] = entry-m if 2*entry > m else entry
        rows.append(row)
    return rows


def equation(n, u, radix, bound, work, power=2):
    """Certify the trace is zero, then return its eliminant in the coordinate (x-u)/R."""
    degree = 2*power
    modulus = radix**degree
    basis = lane_basis(n, u, radix, power)
    scale = [bound**abs(j-power) for j in range(degree+1)]
    weighted = [[c*w for c,w in zip(row, scale)] for row in basis]
    _, coefficients = reduced_basis(weighted, work, initial_coefficients=basis)
    best = min(coefficients, key=lambda r: sum(abs(c)*w for c,w in zip(r, scale)))
    if not any(best) or sum(abs(c)*w for c,w in zip(best, scale)) >= modulus:
        raise ArithmeticError('failed to certify a nonzero auxiliary relation')
    full = [c*n**max(power-j, 0) for j,c in enumerate(best)]
    shifted = [radix**j * sum(comb(i,j)*full[i]*u**(i-j) for i in range(j,degree+1))
               for j in range(degree+1)]
    if any(v % modulus for v in shifted):
        raise ArithmeticError('a Taylor coefficient failed its divisibility check')
    content = gcd(*shifted)
    return [v//content for v in shifted]


def signed_orbit_count(n, radix, ordinary, work):
    """Count unordered residue pairs up to negation, including the fixed pairs."""
    if radix <= 2:
        return ordinary
    roots = 1
    for p, m in prime_powers(radix, work).items():
        work['negation_root_tests'] += 1
        if p == 2:
            level = min(m, 8)
            local = level//2 if (-n) % level == 1 else 0
        else:
            local = 2 if pow(-n, (p-1)//2, p) == 1 else 0
        roots *= local
        if not roots:
            break
    # Each fixed unordered pair is {u,-u}, giving two roots of u²=-n.
    return (ordinary+roots//2)//2


def signed_representatives(pairs, radix, work):
    """Keep one class of each pair exchanged by (u,w) ↦ (-u,-w)."""
    for u, w in pairs:
        work['ordinary_representatives_examined'] += 1
        if radix <= 2 or u+w <= radix:
            yield u, w


def pairs_in_windows(n, u, w, radix, bound, windows, work, power):
    """Solve all signed coordinate bands with one certified lane polynomial."""
    poly = None
    for low_x, high_x in windows:
        lo, hi = -((u-low_x)//radix), (high_x-u)//radix
        if lo > hi:
            continue
        if poly is None:
            poly = equation(n, u, radix, bound, work, power)
        for k in integer_roots(poly, lo, hi, work):
            work['candidate_roots'] += 1
            x = u+radix*k
            if x < 0:
                work['negative_candidate_roots'] += 1
            y, remainder = divmod(n, x)
            small, large = sorted((abs(x), abs(y)))
            if remainder == 0 and small > 1 and y % radix == w and large <= 2*small:
                yield small, large


def search(n, max_orbits=None, *, power=2, signed=False):
    if n < 3 or n % 2 == 0 or (max_orbits is not None and max_orbits < 0):
        raise ValueError('expected odd n >= 3 and a nonnegative optional budget')
    bound, radix = parameters(n, power)
    lower = max(2, isqrt((n-1)//2)+1)
    work, pairs = Counter(), set()
    ordinary, representatives = residue_pairs(n, radix, work)
    total = ordinary
    if signed:
        total = signed_orbit_count(n, radix, ordinary, work)
        representatives = signed_representatives(representatives, radix, work)
    visited, covered = 0, 0
    for _, (u, w) in zip(range(total if max_orbits is None else min(total, max_orbits)), representatives):
        visited += 1
        both = signed and radix > 2 and u+w != radix
        windows = ((lower, bound), (-bound, -lower)) if both else ((lower, bound),)
        covered += len(windows)
        pairs.update(pairs_in_windows(n, u, w, radix, bound, windows, work, power))
    result = dict(n=str(n), power=power, coordinate_bound=bound, radix=radix, total_orbits=total,
                  visited_orbits=visited, remaining_orbits=total-visited,
                  work=dict(work), pairs=[[str(x),str(y)] for x,y in sorted(pairs)])
    if signed:
        result.update(signed=True, ordinary_total_orbits=ordinary, ordinary_covered_orbits=covered)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--max-orbits', type=int)
    parser.add_argument('--power', type=int, default=2, help='largest factor power (polynomial degree is twice this)')
    parser.add_argument('--signed', action='store_true', help='share each polynomial with the negated pair')
    args = parser.parse_args()
    print(json.dumps(search(args.n, args.max_orbits, power=args.power, signed=args.signed), indent=2))
