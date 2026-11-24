"""Compute one gcd over quadratic values in the public interval for the smaller prime."""
import argparse
from collections import defaultdict
import json
from math import gcd, isqrt

from .short_norm_boxes import coordinate_ranges
from .universal_norm_batch import ceil_sqrt, modular_product
from .wide_modulus import product_tree, values_at


def cover(first, stop):
    """Maximal aligned dyadic segments of the half-open interval of array indices."""
    level = 0
    while first < stop:
        if first % 2:
            yield level, first
            first += 1
        if stop % 2:
            stop -= 1
            yield level, stop
        first //= 2
        stop //= 2
        level += 1


def index_range(d, v, lower, upper, side, *, canonical=False):
    """Half-open interval of indices i, where u=2i+1 gives a positive in-band norm."""
    offset = d*v*v
    if d < 0:
        low_square, high_square = lower+offset, upper+offset
    else:
        low_square, high_square = offset-upper, offset-lower
    if high_square < 1:
        return 0, 0
    low = max(1, ceil_sqrt(max(0,low_square)))
    high = min(side, isqrt(high_square))
    if canonical and d == 2:
        high = min(high, v-1)
    # First odd integer at least low is 2*(low//2)+1.
    return low//2, (high+1)//2


def search(n, max_side, *, balanced=False, canonical=False):
    if n < 3 or n % 2 == 0 or max_side < 0:
        raise ValueError('expected odd N >=3 and a nonnegative side cap')
    lower = max(3,ceil_sqrt((n+1)//2)) if balanced else 3
    upper = isqrt(n)
    target = isqrt(upper)
    side = min(max_side,target)
    ranges = coordinate_ranges(lower,upper,side,(-1,-2,2),True)
    requests = defaultdict(list)
    denominators = 0
    pairs = 0
    for d,first,last,step in ranges:
        for v in range(first,last+1,step):
            i, stop = index_range(d,v,lower,upper,side,canonical=canonical)
            if i >= stop:
                continue
            denominators += 1
            pairs += stop-i
            evaluation_point = d*v*v % n
            for node in cover(i,stop):
                requests[node].append(evaluation_point)
    degree, product, evaluations = 0, 1, 0
    if requests:
        roots = [u*u % n for u in range(1,side+1,2)]
        degree = len(roots)
        tree = product_tree(roots,n)
        for (level,index), points in requests.items():
            values = values_at(tree[level][index],points,n)
            product = product*modular_product(values,n) % n
            evaluations += len(points)
    divisor = gcd(product,n)
    found = 1 < divisor < n
    outcome = 'smaller_prime_gcd' if found else ('no_split' if side == target else 'side_limit')
    if divisor == n:
        outcome = 'whole_modulus'
    return dict(factor=divisor if found else None, outcome=outcome, smaller_lower=str(lower),
                smaller_upper=str(upper), side=str(side), target_side=str(target), degree=degree,
                denominators=denominators, allowed_pairs=pairs, polynomial_nodes=len(requests),
                evaluations=evaluations, gcds=1)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n',type=int)
    parser.add_argument('--max-side',type=int,default=128)
    parser.add_argument('--balanced',action='store_true')
    parser.add_argument('--canonical',action='store_true',help='retain the unique normalized prime representation')
    args=parser.parse_args()
    print(json.dumps(search(args.n,args.max_side,balanced=args.balanced,canonical=args.canonical)))
