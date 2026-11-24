"""Batch the public interval for a balanced prime factor using integer-index shifts.

The self-contained interpolation is the Lagrange evaluation in Bostan, Gaudry &
Schost, Theorem 5 (https://doi.org/10.1137/S0097539704443793). The small-prime
wheel follows Costa & Harvey (https://arxiv.org/abs/1201.2116). Here doubling
the step as well as the block length makes all evaluation indices integers.
"""
import argparse
from collections import Counter
from decimal import Decimal, Inexact, MAX_EMAX, MIN_EMIN, localcontext
import json
from math import gcd, isqrt

from .wide_modulus import multiply


def decimal_convolution(left, right, modulus):
    """Pack residues as decimal digits with sufficient room for every carry."""
    length = len(left)+len(right)-1
    digits = len(str(min(len(left), len(right))*(modulus-1)**2))
    template = '{:0'+str(digits)+'d}'
    def packed(coefficients):
        return Decimal(''.join(template.format(x) for x in reversed(coefficients)))
    with localcontext() as context:
        context.prec = digits*length
        context.Emax, context.Emin = MAX_EMAX, MIN_EMIN
        context.traps[Inexact] = True
        product = format(packed(left)*packed(right), 'f').zfill(digits*length)
    return [int(product[end-digits:end]) % modulus for end in range(len(product), 0, -digits)]


def extend_right(values, last, factorial, inverse_factorial, n, convolution, work):
    """Recover F(d+1)..F(last) from F(0)..F(d), for deg(F) <= d."""
    degree = len(values)-1
    if last <= degree:
        return values[:last+1]
    weights = [(v*inverse_factorial[i]*inverse_factorial[degree-i]
                *(-1 if (degree-i) % 2 else 1)) % n for i, v in enumerate(values)]
    reciprocals = [factorial[j-1]*inverse_factorial[j] % n for j in range(1, last+1)]
    mixed = convolution(weights, reciprocals, n)
    work['convolutions'] += 1
    work['convolution_input_coefficients'] += len(weights)+len(reciprocals)
    work['shifted_values'] += last-degree
    return values+[factorial[t]*inverse_factorial[t-degree-1]*mixed[t-1] % n
                   for t in range(degree+1, last+1)]


def block_size(cycles, degree):
    """Choose the dyadic cycle count nearest sqrt(cycles/degree)."""
    size = 1
    while 2*degree*size**2 < cycles:
        size *= 2
    return size


def factorial_tables(last, n, work):
    factorial = [1]
    for j in range(1, last+1):
        factorial.append(factorial[-1]*j % n)
    work['factorial_limit'] = last
    work['setup_gcds'] += 1
    common = gcd(factorial[-1], n)
    if common != 1:
        if common == n:
            for j in range(2, last+1):
                work['setup_gcds'] += 1
                divisor = gcd(j, n)
                if 1 < divisor < n:
                    return None, None, divisor
        return None, None, common
    inverse = [0]*(last+1)
    inverse[-1] = pow(factorial[-1], -1, n)
    work['inversions'] += 1
    for j in range(last, 0, -1):
        inverse[j-1] = inverse[j]*j % n
    return factorial, inverse, None


def wheel_product(start, residues, n):
    value = 1
    for offset in residues:
        value = value*(start+offset) % n
    return value


def block_products(base, cycles, wheel, residues, n, convolution, work):
    """Return products across the full dyadic blocks, and their cycle count."""
    rho = len(residues)
    width = block_size(cycles, rho)
    count = cycles//width
    work['block_cycles'] = width
    work['block_degree'] = width*rho
    work['blocks'] = count
    if width == 1 and count <= rho+1:
        work['seed_terms'] += count*rho
        return [wheel_product(base+j*wheel, residues, n) for j in range(count)], width, None

    # Before the final doubling the inputs are known on 0..rho*width/2.
    # Earlier stages need indices through rho*width+1, and the final one
    # through 2*count-1. The base-only case needs indices through count-1.
    limit = max(rho, rho*width+1 if width > 2 else 0,
                2*count-1 if width > 1 else count-1)
    fact, inv, factor = factorial_tables(limit, n, work)
    if fact is None:
        return [], width, factor
    values = [wheel_product(base+j*wheel, residues, n) for j in range(rho+1)]
    work['seed_terms'] += (rho+1)*rho
    if width == 1:
        return extend_right(values, count-1, fact, inv, n, convolution, work), width, None
    size = 1
    while size < width:
        new_size = 2*size
        needed = count if new_size == width else rho*new_size+1
        enlarged = extend_right(values, 2*needed-1, fact, inv, n, convolution, work)
        values = [enlarged[2*j]*enlarged[2*j+1] % n for j in range(needed)]
        work['paired_products'] += needed
        size = new_size
    return values, width, None


def search(n, max_span, *, wheel=30, backend='decimal'):
    """Assume N=pq for distinct odd p<q<=2p. max_span counts consecutive integers."""
    if n < 3 or n % 2 == 0 or wheel < 2 or (max_span is not None and max_span < 0):
        raise ValueError('expected odd N >= 3, a wheel >= 2, and a nonnegative span cap')
    if backend not in ('decimal', 'binary'):
        raise ValueError('expected decimal or binary convolution')
    convolution = decimal_convolution if backend == 'decimal' else multiply
    # For odd N this is ceil(sqrt(ceil(N/2))).
    first = isqrt((n-1)//2)+1
    upper = isqrt(n)
    span = upper-first+1 if max_span is None else min(max_span, upper-first+1)
    last = first+span-1
    work = Counter()
    def result(factor, outcome, product=None):
        return dict(factor=factor, outcome=outcome, low=str(first), high=str(last),
                    full_high=str(upper), span=str(span), wheel=wheel,
                    interval_complete=product is not None and last == upper, product=None if product is None else str(product),
                    work=dict(work))
    if span <= 0:
        return result(None, 'empty_interval', 1)
    work['setup_gcds'] += 1
    common = gcd(wheel, n)
    if common != 1:
        if common < n:
            return result(common, 'wheel_divisor')
        for candidate in range(2, isqrt(n)+1):
            if wheel % candidate == 0:
                work['setup_gcds'] += 1
                common = gcd(candidate, n)
                if 1 < common < n:
                    return result(common, 'wheel_divisor')
    residues = [j for j in range(1, wheel) if gcd(j, wheel) == 1]
    work['wheel_residues'] = len(residues)
    work['wheel_residue_gcds'] = wheel-1
    base = ((first-1+wheel-1)//wheel)*wheel
    cycles = max(0, (last-base)//wheel)
    full_end = base
    value = 1
    if cycles:
        blocks, width, found = block_products(base, cycles, wheel, residues, n, convolution, work)
        if found is not None and 1 < found < n:
            return result(found, 'interpolation_divisor')
        if found is None:
            for block in blocks:
                value = value*block % n
            full_end = base+len(blocks)*width*wheel
            work['batched_candidates'] = len(blocks)*width*len(residues)
        # If every failed denominator is 0 modulo N, direct evaluation still
        # computes the requested interval product (relevant on tiny prime N).
    for lo, hi in ((first, min(last, base)), (full_end+1, last)):
        if lo > hi:
            continue
        for start in range((lo//wheel)*wheel, hi+1, wheel):
            for r in residues:
                candidate = start+r
                if lo <= candidate <= hi:
                    value = value*candidate % n
                    work['edge_candidates'] += 1
    divisor = gcd(value, n)
    work['final_gcds'] += 1
    if 1 < divisor < n:
        return result(divisor, 'interval_gcd', value)
    if divisor == n:
        return result(None, 'whole_modulus', value)
    return result(None, 'no_split' if last == upper else 'span_limit', value)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--wheel', type=int, default=30)
    parser.add_argument('--backend', choices=('decimal','binary'), default='decimal')
    parser.add_argument('--max-span', type=int, required=True)
    args = parser.parse_args()
    print(json.dumps(search(args.n, args.max_span, wheel=args.wheel, backend=args.backend), indent=2))
