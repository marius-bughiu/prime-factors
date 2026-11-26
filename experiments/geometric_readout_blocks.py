"""Read the same three truncated products by seven scalar products modulo n³."""

from math import gcd, isqrt

from .geometric_sum_readout import _interval, _lane
from .weighted_stride_search import geometric_values, root_polynomial, triangular_powers


def _shape(count):
    width = isqrt(count-1)+1 if count else 0
    groups, tail = divmod(count, width) if width else (0, 0)
    return width, groups, tail


def _scalar_family(q, targets, mod, width, groups, tail, work):
    """One baby polynomial and one common evaluation grid for all these targets."""
    roots = [1]
    for _ in range(1, width):
        roots.append(roots[-1]*q % mod)
    work['baby_roots'] += width
    work['root_polynomials'] += 1
    poly = root_polynomial(roots, mod, stats=work)
    jump = roots[-1]*q % mod
    inverse = pow(jump, -1, mod)
    work['grid_inversions'] += 1
    grid = (triangular_powers(inverse, width+groups, mod),
            triangular_powers(jump, max(width+1, groups), mod))
    work['chirp_entries'] += sum(map(len, grid))

    # Block a contributes jump^(a*width) times P(target*jump^(-a)).
    correction = pow(jump, width*groups*(groups-1)//2, mod)
    work['correction_powers'] += 1
    tail_root = None
    if tail:
        tail_root = pow(jump, groups, mod)
        work['tail_start_powers'] += 1
    tail_roots = []
    for i in range(tail):
        tail_roots.append(tail_root)
        if i+1 < tail:
            tail_root = tail_root*q % mod
    work['tail_roots'] += tail

    products = []
    for target in targets:
        # Scaling the coefficients once handles all geometric block starting points.
        scaled = []
        power = 1
        for i, coefficient in enumerate(poly):
            scaled.append(coefficient*power % mod)
            if i < width:
                power = power*target % mod
        vals = geometric_values(scaled, inverse, groups, mod, grid=grid)
        value = correction
        for v in vals:
            value = value*v % mod
        for r in tail_roots:
            value = value*(target-r) % mod
        products.append(value)
    work['scalar_products'] += len(targets)
    work['scaled_coefficients'] += len(poly)*len(targets)
    work['geometric_convolutions'] += len(targets)
    work['geometric_convolution_inputs'] += (len(poly)+len(grid[0]))*len(targets)
    work['block_evaluations'] += groups*len(targets)
    work['tail_terms'] += tail*len(targets)
    return products


def blocked_coefficients(n, g, y, count):
    """O(sqrt(count)) sample points and polynomial degrees, with no inverse of a root difference."""
    if n < 3 or n%2 == 0 or count < 0 or gcd(g, n) != 1:
        raise ValueError("expected an odd modulus, a unit base, and a nonnegative length")
    width, groups, tail = _shape(count)
    mod = n**3
    work = dict(modulus_bits=mod.bit_length(), block_width=width, blocks_per_scalar=groups,
                tail_per_scalar=tail, validation_gcds=1, scalar_products=0, baby_roots=0,
                root_polynomials=0, tree_leaf_multiplications=0, tree_convolutions=0,
                tree_convolution_inputs=0, grid_inversions=0, chirp_entries=0, correction_powers=0,
                tail_start_powers=0, tail_roots=0, scaled_coefficients=0, geometric_convolutions=0,
                geometric_convolution_inputs=0, block_evaluations=0, tail_terms=0,
                exact_divisions=0)
    if not count:
        return (1, [0, 0, 0], [0, 0, 0]), work

    def family(t, signs):
        return _scalar_family(g*(1+t) % mod, [y*(1+z*t) % mod for z in signs],
                              mod, width, groups, tail, work)

    initial, = family(0, (0,))
    plus = family(n, (0, 1, -1))
    minus = family(-n, (0, 1, -1))
    linear, quadratic = [], []
    half = (n+1)//2
    for upper, lower in zip(plus, minus):
        one, r1 = divmod((upper-lower) % (n*n), n)
        two, r2 = divmod((upper+lower-2*initial) % mod, n*n)
        if r1 or r2:
            raise ArithmeticError("inexact central difference in a geometric product")
        linear.append(one*half % n)
        quadratic.append(two*half % n)
    work['exact_divisions'] = 6
    return (initial % n, linear, quadratic), work


def search(n, base, max_block_width, max_quotient=48):
    """Run the shared decoder only when the baby degree and geometric sample count fit."""
    if max_block_width < 0:
        raise ValueError("expected a nonnegative block width cap")
    term_capacity = max_block_width**2
    lower, upper = _interval(n, base, term_capacity, max_quotient)
    count = upper-lower+1
    width, groups, tail = _shape(count)
    run = _lane(n, base, lower, upper, 1, count, base, term_capacity, max_quotient,
                gcd(base, n), setup_roots=2, setup_gcds=1, reader=blocked_coefficients)
    if run['outcome'] == 'term_limit':
        run['outcome'] = 'block_width_limit'
    run.update(max_block_width=max_block_width, required_width=width,
               blocks_per_scalar=groups, tail_per_scalar=tail)
    return run
