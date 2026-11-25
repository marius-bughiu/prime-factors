"""Search a public interval with integer-valued binomial polynomials.

Rows store coefficients of binom(X,i). Multiplication by degree! produces
an ordinary integral polynomial for divisibility and integer-root checks.
"""

from collections import Counter
from math import comb, factorial, gcd

from .higher_divisor_window import check_row
from .norm_auxiliary import integer_roots, reduced_basis
from .quartic_divisor_window import rootless_prime


def cleared_basis(degree):
    """Return ordinary coefficients of degree! binom(X,i) for i=0,...,degree."""
    denominator = factorial(degree)
    falling = [1]
    rows = []
    for i in range(degree + 1):
        scale = denominator // factorial(i)
        rows.append([scale * a for a in falling] + [0] * (degree - i))
        if i < degree:
            falling = [a - i * b for a, b in zip([0, *falling], [*falling, 0])]
    return rows


def jet_rows(n, anchor, degree, depth, basis):
    """Construct a triangular basis for all rows satisfying the public Taylor congruences."""
    moduli = [n ** (depth - j) for j in range(depth)]
    taylor = []
    inverses = []
    for j, modulus in enumerate(moduli):
        values = [
            sum(row[i] * comb(i, j) * pow(anchor, i - j, modulus)
                for i in range(j, degree + 1)) % modulus
            for row in basis
        ]
        taylor.append(values)
        inverses.append(pow(values[j], -1, modulus))

    rows = []
    for i in range(degree + 1):
        row = [0] * (degree + 1)
        row[i] = n ** max(0, depth - i)
        for j in reversed(range(min(i, depth))):
            residue = -sum(row[l] * taylor[j][l] for l in range(j + 1, i + 1))
            value = residue * inverses[j] % moduli[j]
            row[j] = value - moduli[j] if 2 * value > moduli[j] else value
        rows.append(row)
    return rows


def search(n, first, span, *, degree, depth, modulus_limit=97, centered=False):
    """Check every odd candidate from first through first + 2*span, inclusive.

    With centered=True and even span, the origin is first + span and the signed
    index x of candidate origin + 2*x satisfies |x| <= R = span/2. For i>0
    the exact maximum of |binom(x,i)| is binom(R+i-1,i), attained at x=-R.
    """
    if (n < 3 or n % 2 == 0 or first < 1 or first % 2 == 0 or span < degree
            or not 1 <= depth <= degree or modulus_limit < 0):
        raise ValueError('expected odd input and first candidate, span >= degree >= depth >= 1')
    if centered and span % 2:
        raise ValueError('centered binomial coordinates require an even span')
    radius = span // 2
    origin = first + span if centered else first
    anchor = (n - origin) // 2
    denominator = factorial(degree)
    common = gcd(denominator, n)
    result = dict(lower=first, upper=first + 2 * span, span=span, degree=degree, depth=depth,
                  anchor=anchor, denominator=denominator, denominator_gcd=common, denominator_factor=None,
                  height_bound=first ** depth, progression_size=span + 1, short=False, excluded=False,
                  rootless_modulus=None, divisors=[], work={})
    if centered:
        result.update(centered=True, origin=origin, radius=radius)
    if common != 1:
        # This divisor can lie outside the window.
        if common < n:
            result['denominator_factor'] = common
        else:
            for i in range(2, degree + 1):
                factor = gcd(i, n)
                if 1 < factor < n:
                    result['denominator_factor'] = factor
                    break
        return result

    polynomials = cleared_basis(degree)
    rows = jet_rows(n, anchor, degree, depth, polynomials)
    weights = ([1, *(comb(radius + i - 1, i) for i in range(1, degree + 1))]
               if centered else [comb(span, i) for i in range(degree + 1)])
    scaled = [[a * w for a, w in zip(row, weights)] for row in rows]
    work = Counter(lll_calls=0, lll_swaps=0, lll_reductions=0, moduli_tested=0,
                   modular_evaluations=0, integer_root_nodes=0, divisor_tests=0)
    reduced, basis_rows = reduced_basis(scaled, work, initial_coefficients=rows)
    index = min(range(degree + 1), key=lambda i: sum(map(abs, reduced[i])))
    coefficients = basis_rows[index]
    cleared = [sum(a * row[j] for a, row in zip(coefficients, polynomials)) for j in range(degree + 1)]
    check_row(n, anchor, span, depth, cleared)
    weighted = [a * w for a, w in zip(coefficients, weights)]
    if weighted != reduced[index] or not any(cleared):
        raise ArithmeticError('inconsistent lattice or cleared polynomial')
    height = sum(map(abs, weighted))
    short = height < result['height_bound']
    modulus = rootless_prime(cleared, modulus_limit, work) if short else None
    divisors = []
    if short and modulus is None:
        left, right = (-radius, radius) if centered else (0, span)
        for x in sorted(integer_roots(cleared, left, right, work)):
            d = origin + 2 * x
            work['divisor_tests'] += 1
            if n % d == 0:
                divisors.append(d)
    return dict(result, coefficients=coefficients, cleared_coefficients=cleared, height=height,
                short=short, excluded=short and not divisors, rootless_modulus=modulus,
                divisors=divisors, work=dict(work))
