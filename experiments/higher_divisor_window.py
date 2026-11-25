"""Find and independently check a small polynomial at a prescribed odd location."""

from collections import Counter
from math import comb

from .norm_auxiliary import integer_roots, reduced_basis
from .quartic_divisor_window import rootless_prime


def basis(n, anchor, degree, depth):
    """Rows N^(m-h) X^(i-h) (X-t)^h, h=min(m,i), in ascending powers."""
    rows = []
    for i in range(degree + 1):
        h = min(depth, i)
        start = i - h
        row = [0] * (degree + 1)
        for j in range(h + 1):
            row[start + j] = n**(depth-h) * comb(h, j) * (-anchor)**(h-j)
        rows.append(row)
    return rows


def check_row(n, anchor, radius, depth, row):
    """Check each Taylor coefficient at the anchor against its own modulus."""
    if not any(row):
        raise ValueError('expected a nonzero polynomial')
    for j in range(depth):
        modulus = n**(depth-j)
        value = sum(row[i] * comb(i, j) * pow(anchor, i-j, modulus)
                    for i in range(j, len(row)))
        if value % modulus:
            raise ArithmeticError('polynomial failed its Taylor divisibility check')
    return sum(abs(a) * radius**i for i, a in enumerate(row))


def search(n, center, radius, *, degree, depth, modulus_limit):
    if n < 3 or n % 2 != 1 or center % 2 != 1 or not 1 <= depth <= degree:
        raise ValueError('expected an odd input, an odd center and 1 <= depth <= degree')
    lower, upper = center - 2*radius, center + 2*radius
    if radius < 1 or lower < 1 or modulus_limit < 0:
        raise ValueError('expected a positive window in the divisor range')
    anchor = (n-center) // 2
    scales = [radius**i for i in range(degree + 1)]
    rows = basis(n, anchor, degree, depth)
    scaled = [[a*s for a, s in zip(row, scales)] for row in rows]
    work = Counter(dict(lll_calls=0, lll_swaps=0, lll_reductions=0, moduli_tested=0,
                        modular_evaluations=0, integer_root_nodes=0, divisor_tests=0))
    _, reduced = reduced_basis(scaled, work, initial_coefficients=rows)
    coeff = min(reduced, key=lambda row: sum(abs(a)*s for a, s in zip(row, scales)))
    height = check_row(n, anchor, radius, depth, coeff)
    short = height < lower**depth
    modulus = rootless_prime(coeff, modulus_limit, work) if short else None
    divisors = []
    if short and modulus is None:
        for x in sorted(integer_roots(coeff, -radius, radius, work)):
            d = center + 2*x
            work['divisor_tests'] += 1
            if n % d == 0:
                divisors.append(d)
    return dict(center=center, anchor=anchor, lower=lower, upper=upper, radius=radius,
                degree=degree, depth=depth, progression_size=2*radius+1,
                coefficients=coeff, height=height, height_bound=lower**depth,
                short=short, rootless_modulus=modulus, divisors=divisors,
                excluded=short and not divisors, work=dict(work))
