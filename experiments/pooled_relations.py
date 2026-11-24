"""Combine bounded continued-fraction norm rows from distinct public multipliers."""

from argparse import ArgumentParser
from json import dumps
from math import gcd, isqrt

if __package__:
    from .pell_pairs import convergents
    from .pell_relations import check_rows
else:
    from pell_pairs import convergents
    from pell_relations import check_rows


def search(n, multipliers, max_steps, *, use_gmp=False, external=1):
    """Round-robin walks, stopping each at its center or first period end."""
    if (n <= 1 or isqrt(n)**2 == n or max_steps < 0 or external < 1 or not multipliers
            or any(k <= 0 for k in multipliers) or len(set(multipliers)) != len(multipliers)):
        raise ValueError('expected a nonsquare, distinct positive multipliers and a total step budget')
    work = dict(factor=None, outcome='no_split', steps=0, per_walk=[0]*len(multipliers),
                rows=0, private_pruned=0, pruning_rounds=0, min_private_bits=None,
                dependencies=0, tested=0, selected_steps=[], normalized=0,
                repeated=0, distinct_rows=0, square_tests=0)
    if n % 2 == 0:
        return dict(work, factor=2, outcome='even') if n > 2 else work
    walks = []
    for idx, m in enumerate(multipliers):
        common = gcd(n, m)
        if 1 < common < n:
            return dict(work, factor=common, outcome='multiplier_gcd')
        if common != 1:
            raise ValueError('the input divides a multiplier')
        root = isqrt(m)
        square = m if root*root == m else 1
        walks.append((idx, m, square, convergents(n, m, max_steps)))
    rows = []
    representative = {}
    while walks and work['steps'] < max_steps:
        continuing = []
        for idx, m, square, walk in walks:
            step, denominator, sign, numerator, center = next(walk)
            norm = sign*denominator
            if (numerator**2-norm) % n:
                raise ArithmeticError('incorrect signed convergent norm')
            work['steps'] += 1
            work['per_walk'][idx] += 1
            divisor = gcd(denominator, n)
            if 1 < divisor < n:
                return dict(work, factor=divisor, outcome='denominator')
            if divisor == 1:
                work['rows'] += 1
                common_square = gcd(denominator, square)
                if common_square != 1:
                    scale = isqrt(common_square)
                    if scale*scale != common_square:
                        raise ArithmeticError('scaled numerator gcd is not a square')
                    norm //= common_square
                    numerator = numerator*pow(scale, -1, n) % n
                    work['normalized'] += 1
                if norm in representative:
                    old_label, old_numerator = representative[norm]
                    if numerator not in (old_numerator, n-old_numerator):
                        divisor = gcd(n, numerator-old_numerator)
                        if not 1 < divisor < n:
                            raise ArithmeticError('distinct roots gave no proper divisor')
                        return dict(work, factor=divisor, outcome='equal_norm',
                                    selected_steps=[old_label, [m, step]])
                    work['repeated'] += 1
                else:
                    representative[norm] = ([m, step], numerator)
                    rows.append(([m, step], norm, numerator))
                    work['distinct_rows'] += 1
                    if norm > 0:
                        work['square_tests'] += 1
                        root = isqrt(norm)
                        if root*root == norm:
                            divisor = gcd(numerator-root, n)
                            if 1 < divisor < n:
                                return dict(work, factor=divisor, outcome='square_norm',
                                            selected_steps=[[m, step]])
            if denominator != 1 and not center:
                continuing.append((idx, m, square, walk))
            if work['steps'] == max_steps:
                break
        walks = continuing
    return check_rows(n, rows, work, use_gmp=use_gmp, external=external)


if __name__ == '__main__':
    p = ArgumentParser(description=__doc__)
    p.add_argument('n', type=int)
    p.add_argument('--multipliers', nargs='+', type=int, default=[1, 2])
    p.add_argument('--max-steps', type=int, default=64)
    p.add_argument('--gmp', action='store_true')
    p.add_argument('--external-smooth', type=int)
    args = p.parse_args()
    external = 1
    if args.external_smooth is not None:
        if not args.gmp or args.external_smooth < 1:
            p.error('--external-smooth requires --gmp and a positive bound')
        from gmpy2 import primorial
        external = primorial(args.external_smooth)
    print(dumps(search(args.n, args.multipliers, args.max_steps,
                       use_gmp=args.gmp, external=external)))
