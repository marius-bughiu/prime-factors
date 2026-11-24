"""Find a divisor by batching the values of three binary quadratic forms."""
import argparse
import json
from math import gcd, isqrt

from .mixed_ratio_heights import jacobi
from .wide_modulus import product_tree, values_at


DISCRIMINANTS = (-1, -2, 2)


def ceil_sqrt(n):
    return 0 if n == 0 else 1+isqrt(n-1)


def modular_product(values, n):
    result = 1
    for value in values:
        result = result*value % n
    return result


def search(n, max_side, *, balanced=False):
    """The optional promise is N=pq with distinct odd primes p<q≤2p."""
    if n < 3 or n % 2 == 0 or max_side < 0:
        raise ValueError('expected an odd input >=3 and a nonnegative side cap')
    forms = list(DISCRIMINANTS)
    target = isqrt(isqrt(n))
    if balanced:
        separating = [d for d in forms if jacobi(d,n) == -1]
        if separating:
            # The split prime may be the larger one. Both are at most sqrt(2N).
            forms = separating[:1]
            target = isqrt(isqrt(2*n))
    side = min(target, max_side)
    work = dict(factor=None, outcome='no_split' if side == target else 'side_limit',
                side=str(side), target_side=str(target), discriminants=forms, forms_tested=0,
                empty_forms=0, evaluations=0, degree=0, pair_values_covered=0,
                batch_gcds=0, whole_modulus_batches=0, row_gcds=0, leaf_gcds=0, witness=[])
    if not side:
        return work
    # On the promised input |F(u,v)| below the smaller factor excludes the entire form.
    smallest = ceil_sqrt((n+1)//2) if balanced else 1
    searchable = []
    for d in forms:
        largest_value = (1-d if d < 0 else max(1,d))*side**2
        if largest_value < smallest:
            work['empty_forms'] += 1
        else:
            searchable.append(d)
    if not searchable:
        return dict(work, outcome='below_factor_range')
    residues = [u*u % n for u in range(1, side+1)]
    polynomial = product_tree(residues, n)[-1][0]
    work['degree'] = side
    for d in searchable:
        values = values_at(polynomial, [d*s % n for s in residues], n)
        work['forms_tested'] += 1
        work['evaluations'] += side
        work['pair_values_covered'] += side*side
        work['batch_gcds'] += 1
        aggregate = gcd(modular_product(values,n),n)
        if aggregate == 1:
            continue
        work['whole_modulus_batches'] += int(aggregate == n)
        for v, value in enumerate(values,1):
            work['row_gcds'] += 1
            if gcd(value,n) == 1:
                continue
            for u in range(1, side+1):
                norm = u*u-d*v*v
                work['leaf_gcds'] += 1
                factor = gcd(norm,n)
                if 1 < factor < n:
                    return dict(work, factor=factor, outcome='norm_divisor',
                                witness=[d,str(u),str(v),str(norm)])
    return work


def separating_search(n, max_side, max_selector):
    """One Jacobi-negative coefficient for N=p*q with distinct odd p<q≤2p."""
    if n < 3 or n % 2 == 0 or max_side < 0 or max_selector < 1:
        raise ValueError('expected odd N >= 3, nonnegative side and positive selector cap')
    target = isqrt(isqrt(2*n))
    side = min(target, max_side)
    work = dict(factor=None, outcome='selector_limit', side=str(side), target_side=str(target),
                selector=None, selector_tests=0, evaluations=0, degree=0,
                pair_values_covered=0, batch_gcds=0)
    for b in range(2, min(max_selector, n-1)+1):
        work['selector_tests'] += 1
        sign = jacobi(b,n)
        if sign == 0:
            return dict(work, factor=gcd(b,n), outcome='selector_gcd', selector=b)
        if sign == -1:
            work['selector'] = b
            break
    else:
        return work
    if not side:
        return dict(work, outcome='side_limit')
    squares = [u*u % n for u in range(1, side+1)]
    polynomial = product_tree(squares,n)[-1][0]
    values = values_at(polynomial, [b*s % n for s in squares],n)
    divisor = gcd(modular_product(values,n),n)
    work.update(degree=side, evaluations=side, pair_values_covered=side*side, batch_gcds=1)
    if 1 < divisor < n:
        return dict(work, outcome='separating_gcd', factor=divisor)
    if divisor == n:
        return dict(work, outcome='both_factors_in_batch')
    return dict(work, outcome='side_limit' if side < target else 'no_split')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('n', type=int)
    parser.add_argument('--max-side', type=int, default=128)
    parser.add_argument('--balanced', action='store_true')
    parser.add_argument('--max-selector', type=int, help='use the single separating coefficient on balanced inputs')
    args = parser.parse_args()
    if args.max_selector is not None:
        print(json.dumps(separating_search(args.n, args.max_side, args.max_selector)))
    else:
        print(json.dumps(search(args.n, args.max_side, balanced=args.balanced)))
