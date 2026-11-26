"""Read geometric-product coefficients using blocked scalar samples modulo n² or n³."""

from functools import partial
from math import gcd, isqrt

from .geometric_sum_readout import _interval, _lane
from .reflected_geometric_blocks import reflected_polynomial
from .weighted_stride_search import geometric_values, root_polynomial, triangular_powers


def _shape(count):
    width = isqrt(count-1)+1 if count else 0
    groups, tail = divmod(count, width) if width else (0, 0)
    return width, groups, tail


def _prepare_family(q, mod, width, groups, tail, work, *, reflected_modulus=None):
    """Prepare one baby polynomial and one reusable grid for this geometric base."""
    roots = [1]
    for _ in range(1, width):
        roots.append(roots[-1]*q % mod)
    work['baby_roots'] += width
    poly = None
    if reflected_modulus is not None:
        poly, factor = reflected_polynomial(roots, q, mod, reflected_modulus, work)
        if factor is not None:
            return None
    if poly is None:
        poly = root_polynomial(roots, mod, stats=work)
    work['root_polynomials'] += 1
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

    def evaluate(target):
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
        work['scalar_products'] += 1
        work['scaled_coefficients'] += len(poly)
        work['geometric_convolutions'] += 1
        work['geometric_convolution_inputs'] += len(poly)+len(grid[0])
        work['block_evaluations'] += groups
        work['tail_terms'] += tail
        return value

    return evaluate


def _scalar_family(q, targets, mod, width, groups, tail, work):
    evaluate = _prepare_family(q, mod, width, groups, tail, work)
    return [evaluate(y) for y in targets]


def _setup(n, g, count, precision):
    if n < 3 or n%2 == 0 or count < 0 or gcd(g, n) != 1:
        raise ValueError("expected an odd modulus, a unit base, and a nonnegative length")
    shape = _shape(count)
    return shape, dict(modulus_bits=(n**precision).bit_length(), block_width=shape[0],
                       blocks_per_scalar=shape[1], tail_per_scalar=shape[2],
                       validation_gcds=1, scalar_products=0, baby_roots=0,
                       root_polynomials=0, tree_leaf_multiplications=0, tree_convolutions=0,
                       tree_convolution_inputs=0, grid_inversions=0, chirp_entries=0,
                       correction_powers=0, tail_start_powers=0, tail_roots=0,
                       scaled_coefficients=0, geometric_convolutions=0, geometric_convolution_inputs=0,
                       block_evaluations=0, tail_terms=0, exact_divisions=0)


def _quotient(a, divisor, work):
    value, remainder = divmod(a, divisor)
    if remainder:
        raise ArithmeticError("inexact divided difference in a geometric product")
    work['exact_divisions'] += 1
    return value


def blocked_coefficients(n, g, y, count):
    """Return the full two signed coefficient triples alongside their shared constant."""
    (width, groups, tail), work = _setup(n, g, count, 3)
    mod = n**3
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
        one = _quotient((upper-lower) % (n*n), n, work)
        two = _quotient((upper+lower-2*initial) % mod, n*n, work)
        linear.append(one*half % n)
        quadratic.append(two*half % n)
    return (initial % n, linear, quadratic), work


def _adaptive_coefficients(n, g, y, count, precision):
    """Defer quadratic evaluation until the decoder has exhausted its linear cases."""
    shape, work = _setup(n, g, count, precision)
    work.update(square_products=0, cube_products=0)
    if not count:
        return (1, [0, 0, 0], None), work

    n2, n3 = n*n, n**3

    def evaluator(t, power):
        mod = n**power
        at = _prepare_family(g*(1+t) % mod, mod, *shape, work)
        work['modulus_bits'] = max(work['modulus_bits'], mod.bit_length())
        counter = 'square_products' if power == 2 else 'cube_products'

        def sample(z):
            work[counter] += 1
            return at(y*(1+z*t) % mod)
        return sample

    def first_samples(power):
        zero = evaluator(0, power)(0)
        plus = evaluator(n, power)
        return zero, plus, plus(0), plus(1)

    initial, plus, p0, p1 = first_samples(precision)
    linear0 = _quotient((p0-initial)%n2, n, work)
    linear1 = _quotient((p1-initial)%n2, n, work)
    linear = [linear0, linear1, (2*linear0-linear1)%n]
    if precision == 2:
        plus = None  # The quadratic step needs a cube-precision grid.

    def quadratic():
        if precision == 2:
            # The initial readings modulo n² do not determine their next digit.
            zero, positive, high0, high1 = first_samples(3)
        else:
            zero, positive, high0, high1 = initial, plus, p0, p1
        negative = evaluator(-n, 3)
        low0, low1 = negative(0), negative(1)
        half = (n+1)//2
        half2 = (n2+1)//2
        lift0 = _quotient((high0-low0)%n3, n, work)*half2 % n2
        lift1 = _quotient((high1-low1)%n3, n, work)*half2 % n2
        linear_minus = (2*lift0-lift1) % n2
        return [_quotient((high0+low0-2*zero)%n3, n2, work)*half % n,
                _quotient((high1+low1-2*zero)%n3, n2, work)*half % n,
                _quotient((positive(-1)-zero-n*linear_minus)%n3, n2, work) % n]

    return (initial%n, linear, quadratic), work


def search(n, base, max_block_width, max_quotient=48, *, mode="seven"):
    """Run the shared decoder only when the baby degree and geometric sample count fit."""
    if max_block_width < 0:
        raise ValueError("expected a nonnegative block width cap")
    if mode not in ('seven', 'square_first', 'cube_first'):
        raise ValueError("expected seven, square_first or cube_first")
    reader = blocked_coefficients
    if mode != 'seven':
        precision = 2 if mode == 'square_first' else 3
        reader = partial(_adaptive_coefficients, precision=precision)

    term_capacity = max_block_width**2
    lower, upper = _interval(n, base, term_capacity, max_quotient)
    count = upper-lower+1
    width, groups, tail = _shape(count)
    run = _lane(n, base, lower, upper, 1, count, base, term_capacity, max_quotient,
                gcd(base, n), setup_roots=2, setup_gcds=1, reader=reader)
    if run['outcome'] == 'term_limit':
        run['outcome'] = 'block_width_limit'
    run.update(max_block_width=max_block_width, required_width=width,
               blocks_per_scalar=groups, tail_per_scalar=tail)
    return run
